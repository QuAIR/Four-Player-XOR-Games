/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Refutation
public import Mathlib.Algebra.FreeMonoid.Basic
public import Mathlib.Algebra.Group.Pi.Basic

/-!
# Algebraic commuting-word realizations

This module states the exact algebraic contradiction supplied by an operator
refutation.  A commuting-word realization evaluates one word on every player
page in a common monoid.  It sends profiles whose local words freely reduce to
the identity, and it represents the binary clause-sign phase by a nontrivial
copy of `ZMod 2`.

The construction isolates the group-theoretic content of the usual
commuting-operator argument without making compactness or value-attainment
assumptions.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC uM

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- The one-letter local word contributed by one clause on every player page. -/
def clauseWordProfile
    (query : ClauseId → Clause Player Question) (clause : ClauseId) :
    Player → FreeMonoid Question :=
  fun player => [query clause player]

/-- The player-page word profile obtained by concatenating all clauses in a word. -/
def wordProfile
    (query : ClauseId → Clause Player Question) (word : List ClauseId) :
    Player → FreeMonoid Question :=
  (word.map (clauseWordProfile query)).prod

@[simp]
theorem wordProfile_apply
    (query : ClauseId → Clause Player Question)
    (word : List ClauseId) (player : Player) :
    FreeMonoid.toList (wordProfile query word player) =
      word.map (fun clause => query clause player) := by
  induction word with
  | nil =>
      rfl
  | cons clause tail ih =>
      change
        [query clause player] ++
            FreeMonoid.toList (wordProfile query tail player) =
          query clause player ::
            tail.map (fun c => query c player)
      rw [List.singleton_append, ih]

/--
An algebraic realization of the direct product of the players' involution
words in a common monoid.

Concrete commuting observables induce such a realization: cross-player
commutation makes the pagewise evaluator multiplicative, while local
involution equations give `reduced_eval_one`.
-/
structure CommutingWordRealization
    (Player : Type uP) (Question : Type uQ) (M : Type uM)
    [Monoid M] where
  /-- Multiplicative evaluation of a tuple of local words. -/
  eval : (Player → FreeMonoid Question) →* M
  /-- The binary target-sign phase. -/
  phase : Multiplicative (ZMod 2) →* M
  /-- The odd target phase is genuinely nontrivial. -/
  phase_one_ne_one : phase (Multiplicative.ofAdd 1) ≠ 1
  /-- Locally reducible profiles evaluate to the identity. -/
  reduced_eval_one :
    ∀ profile : Player → FreeMonoid Question,
      (∀ player : Player,
        InvolutionWord.ReducesToEmpty
          (FreeMonoid.toList (profile player))) →
      eval profile = 1

/-- Every clause equation is satisfied exactly in a commuting-word realization. -/
def IsPerfectCommutingWordRealization
    {M : Type uM} [Monoid M]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (realization : CommutingWordRealization Player Question M) : Prop :=
  ∀ clause : ClauseId,
    realization.eval (clauseWordProfile query clause) =
      realization.phase (Multiplicative.ofAdd (sign clause))

private theorem perfect_word_evaluation
    {M : Type uM} [Monoid M]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (realization : CommutingWordRealization Player Question M)
    (hperfect : IsPerfectCommutingWordRealization query sign realization)
    (word : List ClauseId) :
    realization.eval (wordProfile query word) =
      realization.phase
        (Multiplicative.ofAdd ((word.map sign).sum)) := by
  induction word with
  | nil =>
      simp [wordProfile]
  | cons clause tail ih =>
      calc
        realization.eval (wordProfile query (clause :: tail)) =
            realization.eval (clauseWordProfile query clause) *
              realization.eval (wordProfile query tail) := by
                rw [← realization.eval.map_mul]
                rfl
        _ = realization.phase (Multiplicative.ofAdd (sign clause)) *
              realization.phase
                (Multiplicative.ofAdd ((tail.map sign).sum)) := by
              rw [hperfect clause, ih]
        _ = realization.phase
              (Multiplicative.ofAdd (sign clause) *
                Multiplicative.ofAdd ((tail.map sign).sum)) := by
              rw [realization.phase.map_mul]
        _ = realization.phase
              (Multiplicative.ofAdd ((clause :: tail).map sign).sum) := rfl

/--
A true operator refutation excludes every exact perfect commuting-word
realization.

This is the direct algebraic contradiction: balance makes the total word
evaluate to `1`, while odd target parity makes it evaluate to the nontrivial
binary phase.
-/
theorem operatorRefutation_excludes_perfectCommutingWordRealization
    [Fintype ClauseId] [DecidableEq ClauseId]
    {M : Type uM} [Monoid M]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (realization : CommutingWordRealization Player Question M)
    (hrefutation : HasOperatorRefutation query sign) :
    ¬ IsPerfectCommutingWordRealization query sign realization := by
  rintro hperfect
  rcases hrefutation with ⟨word, hbalanced, hodd⟩
  have hevalOne :
      realization.eval (wordProfile query word) = 1 :=
    realization.reduced_eval_one _ fun player => by
      rw [wordProfile_apply]
      exact hbalanced player
  have hsignSum : (word.map sign).sum = 1 := by
    rw [← parityPairing_occurrenceParity]
    exact hodd
  have hevalPhase :=
    perfect_word_evaluation query sign realization hperfect word
  rw [hsignSum] at hevalPhase
  exact realization.phase_one_ne_one (hevalPhase.symm.trans hevalOne)

end

end XORGame
end QIT

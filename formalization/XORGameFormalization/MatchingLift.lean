/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Noncrossing
public import XORGameFormalization.Occurrences
public import Mathlib.Data.Multiset.Filter

/-!
# From simultaneous noncrossing layouts to balanced clause words

The signed occurrence expansion of an integer vector has one vertex for
every unit of positive or negative multiplicity.  A complete linear order of
those vertices, together with a noncrossing equal-question matching on every
player page, directly gives an exact-multiplicity balanced word.

This module formalizes the constructive direction of the four-wire matching
criterion.  It deliberately separates the universal conversion theorem from
the combinatorial work used to construct a common layout.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- A signed occurrence is either one positive or one negative coefficient copy. -/
abbrev SignedOccurrence (y : ClauseId → ℤ) :=
  PositiveOccurrence y ⊕ NegativeOccurrence y

/-- Forget the sign and copy index of a signed occurrence. -/
def signedOccurrenceClause {y : ClauseId → ℤ} :
    SignedOccurrence y → ClauseId
  | Sum.inl occurrence => occurrence.1
  | Sum.inr occurrence => occurrence.1

/-- Read one player's local question from a signed occurrence. -/
def signedOccurrenceQuestion
    (query : ClauseId → Clause Player Question) (player : Player)
    {y : ClauseId → ℤ} (occurrence : SignedOccurrence y) : Question :=
  query (signedOccurrenceClause occurrence) player

/--
A list is a complete occurrence order when it is a permutation of the list
of all signed occurrences.  Thus every individual coefficient copy occurs
exactly once.
-/
def IsCompleteOccurrenceOrder
    [Fintype ClauseId] [DecidableEq ClauseId]
    (y : ClauseId → ℤ) (order : List (SignedOccurrence y)) : Prop :=
  order.Perm (Finset.univ.toList : List (SignedOccurrence y))

private def signedOccurrenceClauseFiberEquiv
    [DecidableEq ClauseId] (y : ClauseId → ℤ) (clause : ClauseId) :
    {occurrence : SignedOccurrence y //
      clause = signedOccurrenceClause occurrence} ≃
      Fin (y clause).toNat ⊕ Fin (-y clause).toNat where
  toFun occurrence := by
    rcases occurrence with ⟨occurrence, hclause⟩
    rcases occurrence with occurrence | occurrence
    · exact Sum.inl (hclause ▸ occurrence.2)
    · exact Sum.inr (hclause ▸ occurrence.2)
  invFun copy := by
    rcases copy with copy | copy
    · exact ⟨Sum.inl ⟨clause, copy⟩, rfl⟩
    · exact ⟨Sum.inr ⟨clause, copy⟩, rfl⟩
  left_inv occurrence := by
    rcases occurrence with ⟨occurrence, hclause⟩
    rcases occurrence with ⟨otherClause, copy⟩ | ⟨otherClause, copy⟩
    · change clause = otherClause at hclause
      subst otherClause
      rfl
    · change clause = otherClause at hclause
      subst otherClause
      rfl
  right_inv copy := by
    rcases copy with copy | copy <;> rfl

private theorem canonicalSignedOccurrenceOrder_clause_count
    [Fintype ClauseId] [DecidableEq ClauseId]
    (y : ClauseId → ℤ) (clause : ClauseId) :
    ((Finset.univ.toList : List (SignedOccurrence y)).map
      signedOccurrenceClause).count clause = (y clause).natAbs := by
  rw [← Multiset.coe_count]
  change Multiset.count clause
      (Multiset.map signedOccurrenceClause
        ((Finset.univ.toList : List (SignedOccurrence y)) :
          Multiset (SignedOccurrence y))) =
    (y clause).natAbs
  rw [Multiset.count_map, Finset.coe_toList]
  change
    (Finset.univ.filter fun occurrence : SignedOccurrence y =>
      clause = signedOccurrenceClause occurrence).card =
        (y clause).natAbs
  calc
    _ = Fintype.card
        {occurrence : SignedOccurrence y //
          clause = signedOccurrenceClause occurrence} := by
      exact (Fintype.card_ofFinset
        (p := {occurrence : SignedOccurrence y |
          clause = signedOccurrenceClause occurrence})
        (Finset.univ.filter fun occurrence : SignedOccurrence y =>
          clause = signedOccurrenceClause occurrence)
        (fun occurrence => by simp)).symm
    _ = Fintype.card
        (Fin (y clause).toNat ⊕ Fin (-y clause).toNat) :=
      Fintype.card_congr
        (signedOccurrenceClauseFiberEquiv y clause)
    _ = (y clause).natAbs := by
      simp [Int.toNat_add_toNat_neg_eq_natAbs]

/--
Reading clause labels from a complete occurrence order gives exactly the
absolute coefficient multiplicities.
-/
theorem completeOccurrenceOrder_clause_count
    [Fintype ClauseId] [DecidableEq ClauseId]
    (y : ClauseId → ℤ) (order : List (SignedOccurrence y))
    (horder : IsCompleteOccurrenceOrder y order) (clause : ClauseId) :
    (order.map signedOccurrenceClause).count clause =
      (y clause).natAbs := by
  have hcount :=
    (horder.map signedOccurrenceClause).count clause
  exact hcount.trans
    (canonicalSignedOccurrenceOrder_clause_count y clause)

/--
A simultaneous noncrossing occurrence layout: the order contains every
signed occurrence once, and each player's question projection admits the
Catalan noncrossing equal-letter recursion.
-/
def HasNoncrossingOccurrenceLayout
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ) : Prop :=
  ∃ order : List (SignedOccurrence y),
    IsCompleteOccurrenceOrder y order ∧
      ∀ player : Player,
        NoncrossingEqualMatching
          (order.map (signedOccurrenceQuestion query player))

/--
Every simultaneous noncrossing occurrence layout yields an
exact-multiplicity balanced clause word.
-/
theorem hasExactMultiplicityBalancedLift_of_noncrossingOccurrenceLayout
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hlayout : HasNoncrossingOccurrenceLayout query y) :
    HasExactMultiplicityBalancedLift query y := by
  rcases hlayout with ⟨order, hcomplete, hmatching⟩
  refine ⟨order.map signedOccurrenceClause, ?_, ?_⟩
  · intro player
    have hreduced :=
      (hmatching player).reducesToEmpty
    simpa [signedOccurrenceQuestion, List.map_map,
      Function.comp_def] using hreduced
  · intro clause
    exact completeOccurrenceOrder_clause_count
      y order hcomplete clause

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import Mathlib.Data.List.Count
public import Mathlib.Data.ZMod.Basic

/-!
# Operator-refutation parity for XOR games

An operator refutation is represented by a clause word whose projection to
every player's local involution generators reduces to the empty word, together
with odd total clause-sign parity.  This module proves the structural
alternating-lift lemma: every such word supplies an integer incidence relation
with the same parity.  Consequently every operator refutation induces a PREF
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:1346-1360].

The local involution and cross-player commutation relations are the relations
of the XOR-game group
[WattsHelton2020ThreeXORGames, main.tex:280-323].
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

namespace InvolutionWord

/--
An involution word reduces to the empty word by repeatedly deleting adjacent
equal letters.

The constructors present the reverse process: start from the empty word and
insert an adjacent pair of equal letters at any position.  Thus a term of this
predicate is an exact finite reduction certificate, not merely an even-count
condition.
-/
inductive ReducesToEmpty {Letter : Type uQ} : List Letter → Prop
  | nil : ReducesToEmpty []
  | insert (left right : List Letter) (letter : Letter)
      (reduced : ReducesToEmpty (left ++ right)) :
      ReducesToEmpty (left ++ letter :: letter :: right)

/-- The integer alternating sum of weights along a word, starting with `+`. -/
def alternatingSum {Letter : Type uQ} (weight : Letter → ℤ) : List Letter → ℤ
  | [] => 0
  | letter :: word => weight letter - alternatingSum weight word

/-- Inserting an adjacent equal pair does not change any alternating sum. -/
theorem alternatingSum_insert_pair {Letter : Type uQ}
    (weight : Letter → ℤ) (left right : List Letter) (letter : Letter) :
    alternatingSum weight (left ++ letter :: letter :: right) =
      alternatingSum weight (left ++ right) := by
  induction left with
  | nil =>
      simp [alternatingSum]
  | cons head tail ih =>
      simpa [alternatingSum] using congrArg (fun z : ℤ => weight head - z) ih

/-- Every alternating sum on a word reducible to empty is zero. -/
theorem ReducesToEmpty.alternatingSum_eq_zero {Letter : Type uQ}
    {word : List Letter} (hword : ReducesToEmpty word) (weight : Letter → ℤ) :
    alternatingSum weight word = 0 := by
  induction hword with
  | nil =>
      rfl
  | insert left right letter reduced ih =>
      rw [alternatingSum_insert_pair]
      exact ih

/-- Alternating sums commute with mapping a word. -/
theorem alternatingSum_map {Letter : Type uQ} {Letter' : Type uP}
    (weight : Letter' → ℤ) (f : Letter → Letter') (word : List Letter) :
    alternatingSum weight (word.map f) =
      alternatingSum (weight ∘ f) word := by
  induction word with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [alternatingSum, ih, Function.comp_apply]

end InvolutionWord

/--
A clause word is balanced when every player projection reduces to the empty
word using the local involution relations.
-/
def IsBalancedWord
    (query : ClauseId → Clause Player Question) (word : List ClauseId) : Prop :=
  ∀ player : Player,
    InvolutionWord.ReducesToEmpty (word.map fun c => query c player)

/--
The alternating integer lift of a clause word.

At zero-based even positions an occurrence contributes `+1`; at odd positions
it contributes `-1`.
-/
def alternatingLift [DecidableEq ClauseId] : List ClauseId → ClauseId → ℤ
  | [], _ => 0
  | clause :: word, c =>
      (if c = clause then 1 else 0) - alternatingLift word c

/-- Pairing a coefficient vector with the alternating lift gives its wordwise alternating sum. -/
theorem sum_mul_alternatingLift [Fintype ClauseId] [DecidableEq ClauseId]
    (weight : ClauseId → ℤ) (word : List ClauseId) :
    ∑ c : ClauseId, weight c * alternatingLift word c =
      InvolutionWord.alternatingSum weight word := by
  induction word with
  | nil =>
      simp [alternatingLift, InvolutionWord.alternatingSum]
  | cons clause tail ih =>
      calc
        ∑ c : ClauseId, weight c * alternatingLift (clause :: tail) c =
            (∑ c : ClauseId, weight c * (if c = clause then 1 else 0)) -
              ∑ c : ClauseId, weight c * alternatingLift tail c := by
                simp only [alternatingLift, mul_sub, Finset.sum_sub_distrib]
        _ = weight clause -
              ∑ c : ClauseId, weight c * alternatingLift tail c := by
                simp
        _ = weight clause - InvolutionWord.alternatingSum weight tail := by
                rw [ih]
        _ = InvolutionWord.alternatingSum weight (clause :: tail) := by
                rfl

/--
The alternating lift of a balanced clause word is an integer relation among
the incidence rows.
-/
theorem balancedWord_alternatingLift_isIntegerRelation
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (word : List ClauseId)
    (hword : IsBalancedWord query word) :
    IsIntegerRelation query (alternatingLift word) := by
  intro pq
  rcases pq with ⟨player, question⟩
  rw [sum_mul_alternatingLift]
  have hzero :=
    (hword player).alternatingSum_eq_zero
      (fun q : Question => if q = question then 1 else 0)
  rw [InvolutionWord.alternatingSum_map] at hzero
  simpa [incidence, Function.comp_apply] using hzero

/-- Coordinatewise parity of an integer incidence relation. -/
def relationParity (y : ClauseId → ℤ) : ClauseId → ZMod 2 :=
  fun c => y c

/-- Mod-two occurrence count of each clause in a word. -/
def occurrenceParity [DecidableEq ClauseId]
    (word : List ClauseId) : ClauseId → ZMod 2 :=
  fun c => word.count c

/-- Modulo two, the alternating lift is exactly clause-occurrence parity. -/
theorem alternatingLift_mod_two_apply [DecidableEq ClauseId]
    (word : List ClauseId) (c : ClauseId) :
    relationParity (alternatingLift word) c = occurrenceParity word c := by
  induction word with
  | nil =>
      simp [alternatingLift, relationParity, occurrenceParity]
  | cons clause tail ih =>
      have ih' : (alternatingLift tail c : ZMod 2) =
          (tail.count c : ZMod 2) := by
        simpa [relationParity, occurrenceParity] using ih
      by_cases h : clause = c
      · subst clause
        simp [alternatingLift, relationParity, occurrenceParity,
          ih', sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]
      · simp [alternatingLift, relationParity, occurrenceParity,
          h, Ne.symm h, ih', sub_eq_add_neg, ZMod.neg_eq_self_mod_two]

/-- Function form of parity preservation by the alternating lift. -/
theorem alternatingLift_mod_two [DecidableEq ClauseId]
    (word : List ClauseId) :
    relationParity (alternatingLift word) = occurrenceParity word := by
  funext c
  exact alternatingLift_mod_two_apply word c

/-- The mod-two pairing of a clause-sign vector with a clause parity vector. -/
def parityPairing [Fintype ClauseId]
    (sign parity : ClauseId → ZMod 2) : ZMod 2 :=
  ∑ c : ClauseId, sign c * parity c

/--
Pairing a sign vector with word-occurrence parity is the sum of the signs
encountered along the word.
-/
theorem parityPairing_occurrenceParity
    [Fintype ClauseId] [DecidableEq ClauseId]
    (sign : ClauseId → ZMod 2) (word : List ClauseId) :
    parityPairing sign (occurrenceParity word) =
      (word.map sign).sum := by
  induction word with
  | nil =>
      simp [parityPairing, occurrenceParity]
  | cons clause tail ih =>
      simp only [List.map_cons, List.sum_cons, ← ih]
      simp [parityPairing, occurrenceParity, List.count_cons, mul_add,
        Finset.sum_add_distrib, add_comm]

/--
An integer PREF witness is an integer incidence relation with odd sign
pairing.
-/
def IsPREF [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) (y : ClauseId → ℤ) : Prop :=
  IsIntegerRelation query y ∧ parityPairing sign (relationParity y) = 1

/-- A signed clause family contains a PREF when it has an integer PREF witness. -/
def HasPREF [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) : Prop :=
  ∃ y : ClauseId → ℤ, IsPREF query sign y

/--
A clause word is an operator refutation when it is balanced and has odd total
clause-sign parity.
-/
def IsOperatorRefutation [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) (word : List ClauseId) : Prop :=
  IsBalancedWord query word ∧ parityPairing sign (occurrenceParity word) = 1

/-- A signed clause family admits an operator refutation when it has such a word. -/
def HasOperatorRefutation [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) : Prop :=
  ∃ word : List ClauseId, IsOperatorRefutation query sign word

/--
Every operator refutation of a finite XOR game induces a PREF.

The witness is the alternating integer lift of the refutation word.  Its
balanced player projections force the incidence relation, while reduction
modulo two forgets alternating signs and retains occurrence parity.  This
formalizes the necessary condition for refutations
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:1346-1360].
-/
theorem operatorRefutation_implies_pref
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (sign : ClauseId → ZMod 2) :
    HasOperatorRefutation query sign → HasPREF query sign := by
  rintro ⟨word, hbalanced, hodd⟩
  refine ⟨alternatingLift word,
    balancedWord_alternatingLift_isIntegerRelation query word hbalanced, ?_⟩
  rw [alternatingLift_mod_two]
  exact hodd

end

end XORGame
end QIT

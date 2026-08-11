/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Spaces

/-!
# Exact-multiplicity balanced lifts

The structural circuit arguments construct a balanced clause word containing
clause `c` exactly `natAbs (y c)` times.  This module records the general
bridge from that stronger integer statement to the binary balanced-lift
property needed by the parity-space argument.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

namespace InvolutionWord

/-- Concatenating two words reducible to empty again reduces to empty. -/
theorem ReducesToEmpty.append {left right : List Question}
    (hleft : ReducesToEmpty left) (hright : ReducesToEmpty right) :
    ReducesToEmpty (left ++ right) := by
  induction hleft with
  | nil =>
      simpa using hright
  | insert before after letter reduced ih =>
      have ih' : ReducesToEmpty (before ++ (after ++ right)) := by
        simpa [List.append_assoc] using ih
      simpa [List.append_assoc] using
        ReducesToEmpty.insert before (after ++ right) letter ih'

end InvolutionWord

/-- Balanced clause words are closed under concatenation. -/
theorem IsBalancedWord.append
    (query : ClauseId → Clause Player Question)
    {left right : List ClauseId}
    (hleft : IsBalancedWord query left)
    (hright : IsBalancedWord query right) :
    IsBalancedWord query (left ++ right) := by
  intro player
  simpa [List.map_append] using
    (hleft player).append (hright player)

/--
An exact-multiplicity balanced lift of an integer coefficient vector is a
balanced word in which each clause occurs exactly the absolute value of its
coefficient many times.
-/
def HasExactMultiplicityBalancedLift
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ) : Prop :=
  ∃ word : List ClauseId,
    IsBalancedWord query word ∧
      ∀ clause : ClauseId, word.count clause = (y clause).natAbs

/--
Exact integer multiplicities imply equality of binary occurrence parity and
relation parity.
-/
theorem exactMultiplicityBalancedLift_hasBalancedLift
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hlift : HasExactMultiplicityBalancedLift query y) :
    HasBalancedLift query y := by
  rcases hlift with ⟨word, hbalanced, hcount⟩
  refine ⟨word, hbalanced, ?_⟩
  funext clause
  simp [occurrenceParity, relationParity, hcount clause]

namespace HasBalancedLift

/-- The zero coefficient vector is lifted by the empty word. -/
theorem zero [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) :
    HasBalancedLift query 0 := by
  refine ⟨[], ?_, ?_⟩
  · intro player
    exact InvolutionWord.ReducesToEmpty.nil
  · funext clause
    simp [occurrenceParity, relationParity]

/-- Balanced lifts are closed under addition by concatenating their words. -/
theorem add [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    {left right : ClauseId → ℤ}
    (hleft : HasBalancedLift query left)
    (hright : HasBalancedLift query right) :
    HasBalancedLift query (left + right) := by
  rcases hleft with ⟨leftWord, hleftBalanced, hleftParity⟩
  rcases hright with ⟨rightWord, hrightBalanced, hrightParity⟩
  refine ⟨leftWord ++ rightWord,
    hleftBalanced.append query hrightBalanced, ?_⟩
  funext clause
  have hleftClause := congrFun hleftParity clause
  have hrightClause := congrFun hrightParity clause
  change (leftWord.count clause : ZMod 2) = (left clause : ZMod 2) at hleftClause
  change (rightWord.count clause : ZMod 2) = (right clause : ZMod 2) at hrightClause
  simp only [occurrenceParity, List.count_append, Nat.cast_add,
    relationParity, Pi.add_apply, Int.cast_add]
  rw [hleftClause, hrightClause]

/--
Negation does not change a coefficient vector modulo two, so the same word
lifts its negative.
-/
theorem neg [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    {y : ClauseId → ℤ} (hy : HasBalancedLift query y) :
    HasBalancedLift query (-y) := by
  rcases hy with ⟨word, hbalanced, hparity⟩
  refine ⟨word, hbalanced, ?_⟩
  funext clause
  have hclause := congrFun hparity clause
  simpa [relationParity, ZMod.neg_eq_self_mod_two] using hclause

end HasBalancedLift

/--
Coefficient vectors whose parity has a balanced lift form an additive
subgroup of the integer coefficient lattice.
-/
def balancedLiftAddSubgroup
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) :
    AddSubgroup (ClauseId → ℤ) where
  carrier := {y | HasBalancedLift query y}
  zero_mem' := HasBalancedLift.zero query
  add_mem' := fun hleft hright => hleft.add query hright
  neg_mem' := fun hy => hy.neg query

/--
If a family of integer vectors has balanced lifts, then every vector in its
additive subgroup closure has a balanced lift.
-/
theorem hasBalancedLift_of_mem_addSubgroup_closure
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    (generators : Set (ClauseId → ℤ))
    (hlift :
      ∀ y : ClauseId → ℤ, y ∈ generators → HasBalancedLift query y)
    {y : ClauseId → ℤ} (hy : y ∈ AddSubgroup.closure generators) :
    HasBalancedLift query y := by
  have hclosure :
      AddSubgroup.closure generators ≤ balancedLiftAddSubgroup query :=
    (balancedLiftAddSubgroup query).closure_le.mpr
      (fun generator hgenerator => hlift generator hgenerator)
  exact hclosure hy

/--
It is enough to construct exact-multiplicity balanced words for all integer
relations in order to obtain the support-level parity lifting property.
-/
theorem everyIntegerRelationHasBalancedLift_of_exactMultiplicity
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (hlift :
      ∀ y : ClauseId → ℤ,
        IsIntegerRelation query y →
          HasExactMultiplicityBalancedLift query y) :
    EveryIntegerRelationHasBalancedLift query := by
  intro y hy
  exact exactMultiplicityBalancedLift_hasBalancedLift query y (hlift y hy)

end

end XORGame
end QIT

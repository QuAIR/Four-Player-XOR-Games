/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.CircuitSupport
public import XORGameFormalization.Lift

/-!
# Transporting balanced lifts off an integer support

Cardinality-sensitive theorems naturally work on the nonzero support of a
primitive integer circuit.  A word over that subtype becomes a word over
the original clause index by applying `Subtype.val`.  This module proves
that exact multiplicities and all player reductions survive that inclusion.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
An exact-multiplicity lift of a coefficient vector restricted to its
nonzero support extends to an exact-multiplicity lift on the original
clause index.
-/
theorem exactMultiplicityBalancedLift_of_integerSupport
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hlift :
      HasExactMultiplicityBalancedLift
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)) :
    HasExactMultiplicityBalancedLift query c := by
  rcases hlift with ⟨word, hbalanced, hcount⟩
  refine ⟨word.map Subtype.val, ?_, ?_⟩
  · intro player
    have hreduced := hbalanced player
    simpa [restrictQueryToIntegerSupport, List.map_map,
      Function.comp_def] using hreduced
  · intro clause
    by_cases hclause : clause ∈ integerSupport c
    · let supportedClause : ↥(integerSupport c) :=
        ⟨clause, hclause⟩
      have hmapCount :=
        @List.count_map_of_injective
          _ _ (instBEqOfDecidableEq) (by infer_instance)
          (instBEqOfDecidableEq) (by infer_instance)
          word Subtype.val Subtype.val_injective supportedClause
      have hrestrictedCount := hcount supportedClause
      exact hmapCount.trans hrestrictedCount
    · have hcoefficient : c clause = 0 := by
        simpa [mem_integerSupport] using hclause
      have hnotmem :
          clause ∉ word.map
            (Subtype.val : ↥(integerSupport c) → E) := by
        simp [hclause]
      rw [List.count_eq_zero.mpr hnotmem, hcoefficient]
      rfl

/--
A support-restricted exact lift also gives the parity-level balanced lift on
the original clause index.
-/
theorem balancedLift_of_exactLift_on_integerSupport
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hlift :
      HasExactMultiplicityBalancedLift
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)) :
    HasBalancedLift query c :=
  exactMultiplicityBalancedLift_hasBalancedLift query c
    (exactMultiplicityBalancedLift_of_integerSupport
      query c hlift)

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.HardCenterGeometry
public import XORGameFormalization.TenStructural

/-!
# Matching escape interface for the ten-clause boundary

The same two local matching escapes used at nine clauses also close the
ten-clause boundary.  Full-circuit rank forces all four pages to be ternary;
odd-layer escape gives even support distances, and shared-block escape gives
safe-center separation.  The covering/noncovering structural assembly then
proves the exact lift.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
Odd-layer and shared-block matching escapes imply exact liftability for
every ten-clause full rational circuit.
-/
theorem tenClause_exactLift_of_oddLayer_and_sharedBlock_escapes
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 10)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (hoddEscape :
      ∀ center ∈ safeCenters (Finset.univ.image query),
        ¬ EvenSupportDistances query center →
          HasExactMultiplicityBalancedLift query y)
    (hsharedEscape :
      ∀ x yCenter : FourByThreeClause,
        HasSharedThirdQuestionBlockMissingCell query x yCenter →
          HasExactMultiplicityBalancedLift query y) :
    HasExactMultiplicityBalancedLift query y := by
  have hnonemptyE : Nonempty E := by
    rw [← Fintype.card_pos_iff]
    omega
  letI : Nonempty E := hnonemptyE
  have hternary :
      ∀ player : FourByThreePlayer,
        usedQuestionsCard query player = 3 :=
    tenClause_fullCircuit_uses_all_questions
      query hcard hCircuit
  apply tenClause_exactLift_of_nonliftable_even_separated
    query y hquery hcard hCircuit
  · intro hnotLift center hcenter clause hclause
    have hcenterEven : EvenSupportDistances query center := by
      by_contra hnotEven
      exact hnotLift (hoddEscape center hcenter hnotEven)
    obtain ⟨clauseIndex, _hclauseIndex, rfl⟩ :=
      Finset.mem_image.mp hclause
    exact hcenterEven clauseIndex
  · intro hnotLift u hu v hv huv
    have huEven : EvenSupportDistances query u := by
      by_contra hnotEven
      exact hnotLift (hoddEscape u hu hnotEven)
    have hvEven : EvenSupportDistances query v := by
      by_contra hnotEven
      exact hnotLift (hoddEscape v hv hnotEven)
    exact
      evenSupportDistances_separated_of_sharedBlockMissingCell_escape
        query (by omega) hternary
        (HasExactMultiplicityBalancedLift query y)
        hsharedEscape hnotLift u v huv huEven hvEven

end

end XORGame
end QIT

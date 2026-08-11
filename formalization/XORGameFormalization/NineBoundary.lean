/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.HardCenterGeometry
public import XORGameFormalization.NineStructural

/-!
# Matching escape interface for the nine-clause boundary

The nine-clause Hamming contradiction needs only two reusable matching
escapes:

* an odd support layer about a safe center gives an exact lift;
* the shared-third-question-block/missing-cell configuration gives an exact
  lift.

This module proves that those two local statements imply the complete
four-ternary nine-clause lift theorem.  In particular, the remaining
matching work is named exactly and no numerical census is hidden in the
boundary proof.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
Odd-layer and shared-block escapes close the four-ternary nine-clause
boundary by the safe-center packing contradiction.
-/
theorem nineClause_exactLift_of_oddLayer_and_sharedBlock_escapes
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (hternary :
      ∀ player : FourByThreePlayer,
        usedQuestionsCard query player = 3)
    (hoddEscape :
      ∀ center ∈ safeCenters (Finset.univ.image query),
        ¬ EvenSupportDistances query center →
          HasExactMultiplicityBalancedLift query y)
    (hsharedEscape :
      ∀ x yCenter : FourByThreeClause,
        HasSharedThirdQuestionBlockMissingCell query x yCenter →
          HasExactMultiplicityBalancedLift query y) :
    HasExactMultiplicityBalancedLift query y := by
  apply nineClause_exactLift_of_nonliftable_even_separated
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

/--
Complete nine-clause interface: the three-complex-page theorem handles the
`(3,3,3,2)` branch, and the safe-center escapes handle four ternary pages.
-/
theorem nineClause_exactLift_of_threePage_and_safeCenter_escapes
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (hthreePage :
      (ternaryPlayers query).card ≤ 3 →
        HasExactMultiplicityBalancedLift query y)
    (hoddEscape :
      ∀ center ∈ safeCenters (Finset.univ.image query),
        ¬ EvenSupportDistances query center →
          HasExactMultiplicityBalancedLift query y)
    (hsharedEscape :
      ∀ x yCenter : FourByThreeClause,
        HasSharedThirdQuestionBlockMissingCell query x yCenter →
          HasExactMultiplicityBalancedLift query y) :
    HasExactMultiplicityBalancedLift query y := by
  rcases ternaryPlayers_card_le_three_or_all query with
    hthree | hall
  · exact hthreePage hthree
  · exact
      nineClause_exactLift_of_oddLayer_and_sharedBlock_escapes
        query y hquery hcard hCircuit hall
          hoddEscape hsharedEscape

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.HardCenterGeometry
public import XORGameFormalization.SmallStructural

/-!
# Four-ternary matching escape interface below nine clauses

The odd-layer and shared-block escapes turn nonliftability into the even,
separated safe-center geometry.  Below nine clauses the global excess
inequality contradicts that geometry immediately.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
For four ternary pages and at most eight distinct clauses, the two local
matching escapes imply exact liftability uniformly.
-/
theorem
    atMostEight_fourTernary_exactLift_of_oddLayer_and_sharedBlock_escapes
    {E : Type uE} [Fintype E] [Nonempty E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E ≤ 8)
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
  apply atMostEight_exactLift_of_nonliftable_even_separated
    query y hquery hcard
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
Complete sub-nine interface: the three-complex-page theorem handles at most
three ternary pages, while the safe-center escapes handle the all-ternary
case.
-/
theorem atMostEight_exactLift_of_threePage_and_safeCenter_escapes
    {E : Type uE} [Fintype E] [Nonempty E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E ≤ 8)
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
      atMostEight_fourTernary_exactLift_of_oddLayer_and_sharedBlock_escapes
        query y hquery hcard hall hoddEscape hsharedEscape

end

end XORGame
end QIT

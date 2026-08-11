/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.PrimitiveCircuitWindows
public import XORGameFormalization.SmallBoundary
public import XORGameFormalization.NineBoundary
public import XORGameFormalization.TenBoundary
public import XORGameFormalization.SafeCenterLift

/-!
# Closing the three primitive-circuit windows from matching escapes

This module is the structural join point of the proof.  Three reusable
matching results are applied on every primitive support:

* the at-most-three-ternary-page lift;
* odd-layer singleton escape at a safe center;
* shared-third-question-block escape.

The sub-nine excess contradiction and the nine- and ten-clause boundary
theorems then prove every primitive circuit liftable.  The rank-ten theorem
shows that these three windows are exhaustive.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
The three general matching escapes imply the primitive-circuit lifting
hypothesis for every distinct-clause four-by-three query.
-/
theorem primitiveCircuit_lifts_of_structural_matching_escapes
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hthreePage :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (ternaryPlayers
          (restrictQueryToIntegerSupport query c)).card ≤ 3 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hoddEscape :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        ∀ center ∈ safeCenters
          (Finset.univ.image
            (restrictQueryToIntegerSupport query c)),
          ¬ EvenSupportDistances
              (restrictQueryToIntegerSupport query c) center →
            HasSupportExactMultiplicityBalancedLift query c)
    (hsharedEscape :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        ∀ x yCenter : FourByThreeClause,
          HasSharedThirdQuestionBlockMissingCell
              (restrictQueryToIntegerSupport query c) x yCenter →
            HasSupportExactMultiplicityBalancedLift query c) :
    ∀ c : E → ℤ,
      IsPrimitiveKernelCircuit
          (incidenceRelationHom query) c →
      HasBalancedLift query c := by
  apply primitiveCircuit_lifts_of_support_windows query
  · intro c hc hcard
    letI : Nonempty ↥(integerSupport c) :=
      Finset.nonempty_coe_sort.mpr
        (primitiveKernelCircuit_integerSupport_nonempty
          (incidenceRelationHom query) c hc)
    exact
      atMostEight_exactLift_of_threePage_and_safeCenter_escapes
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)
        (restrictQueryToIntegerSupport_injective
          query c hquery)
        (by
          rw [Fintype.card_coe]
          exact hcard)
        (hthreePage c hc)
        (hoddEscape c hc)
        (hsharedEscape c hc)
  · intro c hc hcard
    letI : Nonempty ↥(integerSupport c) :=
      Finset.nonempty_coe_sort.mpr
        (primitiveKernelCircuit_integerSupport_nonempty
          (incidenceRelationHom query) c hc)
    exact
      nineClause_exactLift_of_threePage_and_safeCenter_escapes
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)
        (restrictQueryToIntegerSupport_injective
          query c hquery)
        (by
          rw [Fintype.card_coe]
          exact hcard)
        (primitiveKernelCircuit_restricted_isFullRationalCircuit
          query c hc)
        (hthreePage c hc)
        (hoddEscape c hc)
        (hsharedEscape c hc)
  · intro c hc hcard
    letI : Nonempty ↥(integerSupport c) :=
      Finset.nonempty_coe_sort.mpr
        (primitiveKernelCircuit_integerSupport_nonempty
          (incidenceRelationHom query) c hc)
    exact
      tenClause_exactLift_of_oddLayer_and_sharedBlock_escapes
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)
        (restrictQueryToIntegerSupport_injective
          query c hquery)
        (by
          rw [Fintype.card_coe]
          exact hcard)
        (primitiveKernelCircuit_restricted_isFullRationalCircuit
          query c hc)
        (hoddEscape c hc)
        (hsharedEscape c hc)

/--
After discharging the three-ternary-page and shared-block theorems, only the
odd safe-center escape remains as an input to the global structural assembly.
-/
theorem primitiveCircuit_lifts_of_odd_safeCenter_escape
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hoddEscape :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        ∀ center ∈ safeCenters
          (Finset.univ.image
            (restrictQueryToIntegerSupport query c)),
          ¬ EvenSupportDistances
              (restrictQueryToIntegerSupport query c) center →
            HasSupportExactMultiplicityBalancedLift query c) :
    ∀ c : E → ℤ,
      IsPrimitiveKernelCircuit
          (incidenceRelationHom query) c →
      HasBalancedLift query c := by
  apply primitiveCircuit_lifts_of_structural_matching_escapes
    query hquery
  · intro c hc hpages
    change HasExactMultiplicityBalancedLift
      (restrictQueryToIntegerSupport query c)
      (fun clause : ↥(integerSupport c) => c clause.1)
    apply hasExactMultiplicityBalancedLift_of_ternaryPlayers_card_le_three
      (restrictQueryToIntegerSupport query c)
      (fun clause : ↥(integerSupport c) => c clause.1)
      (primitiveKernelCircuit_restricted_isIntegerRelation query c hc)
      hpages
    rw [Fintype.card_coe]
    exact (primitiveIncidenceCircuit_support_card_le_ten query c hc).trans
      (by omega)
  · exact hoddEscape
  · intro c hc x yCenter hshared
    change HasExactMultiplicityBalancedLift
      (restrictQueryToIntegerSupport query c)
      (fun clause : ↥(integerSupport c) => c clause.1)
    exact
      hasExactMultiplicityBalancedLift_of_sharedThirdQuestionBlockMissingCell
        (restrictQueryToIntegerSupport query c)
        (fun clause : ↥(integerSupport c) => c clause.1)
        (primitiveKernelCircuit_restricted_isIntegerRelation query c hc)
        x yCenter hshared

/-- Every primitive circuit of an injective four-player three-question query
has a balanced lift.  This closes the final abstract safe-center input in the
structural-window assembly. -/
theorem primitiveCircuit_lifts_fourByThree
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query) :
    ∀ c : E → ℤ,
      IsPrimitiveKernelCircuit
          (incidenceRelationHom query) c →
      HasBalancedLift query c := by
  apply primitiveCircuit_lifts_of_odd_safeCenter_escape query hquery
  intro c hc center hcenter hodd
  change HasExactMultiplicityBalancedLift
    (restrictQueryToIntegerSupport query c)
    (fun clause : ↥(integerSupport c) => c clause.1)
  exact hasExactMultiplicityBalancedLift_of_odd_safeCenter
    (restrictQueryToIntegerSupport query c)
    (fun clause : ↥(integerSupport c) => c clause.1)
    (primitiveKernelCircuit_restricted_isIntegerRelation query c hc)
    center hcenter
    (integerSupport_coefficient_ne_zero c)
    hodd

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.CircuitGeneration
public import XORGameFormalization.CommutingWord
public import XORGameFormalization.ObservableStrategy
public import XORGameFormalization.PrimitiveCircuitWindows
public import XORGameFormalization.Spaces
public import XORGameFormalization.StructuralWindows

/-!
# Structural assembly for perfect XOR games

This module isolates the final abstract assembly.  Integral circuit generation
reduces an arbitrary PREF to primitive circuit directions.  If those
directions have balanced lifts, the PREF becomes a true operator refutation,
which excludes every exact perfect commuting-word realization and forces the
MERP parity condition.

The four-by-three boundary modules discharge the primitive-circuit lifting
hypothesis; keeping the assembly generic makes the logical dependency
explicit.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC uM

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/--
If every primitive integer incidence circuit has a balanced lift, every PREF
can be upgraded to a true operator refutation.
-/
theorem operatorRefutation_of_pref_of_primitiveCircuit_lifts
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c) :
    HasPREF query sign → HasOperatorRefutation query sign := by
  exact
    hasOperatorRefutation_of_pref_of_everyIntegerRelationHasBalancedLift
      query sign
      (everyIntegerRelationHasBalancedLift_of_primitiveCircuits query hlift)

/--
Under primitive-circuit liftability, a PREF excludes every exact perfect
commuting-word realization.
-/
theorem pref_excludes_perfectCommutingWordRealization_of_primitiveCircuit_lifts
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    {M : Type uM} [Monoid M]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (realization : CommutingWordRealization Player Question M)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c)
    (hpref : HasPREF query sign) :
    ¬ IsPerfectCommutingWordRealization query sign realization :=
  operatorRefutation_excludes_perfectCommutingWordRealization
    query sign realization
    (operatorRefutation_of_pref_of_primitiveCircuit_lifts
      query sign hlift hpref)

/--
Under primitive-circuit liftability, every exact perfect commuting-word
realization satisfies the MERP parity condition.
-/
theorem
    perfectCommutingWordRealization_implies_merpPerfectParity_of_primitiveCircuit_lifts
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    {M : Type uM} [Monoid M]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (realization : CommutingWordRealization Player Question M)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c)
    (hperfect : IsPerfectCommutingWordRealization query sign realization) :
    IsMERPPerfectParity query sign := by
  by_contra hnotMERP
  have hpref : HasPREF query sign := by
    exact Classical.byContradiction fun hnopref =>
      hnotMERP
        ((isMERPPerfectParity_iff_not_hasPREF query sign).mpr hnopref)
  exact
    (pref_excludes_perfectCommutingWordRealization_of_primitiveCircuit_lifts
      query sign realization hlift hpref) hperfect

/--
Under primitive-circuit liftability, a PREF excludes a concrete perfect
four-player commuting-observable strategy.
-/
theorem
    pref_excludes_perfectFourPlayerBinaryObservableStrategy_of_primitiveCircuit_lifts
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    {Hilbert : Type*} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c)
    (hpref : HasPREF query sign) :
    ¬ IsPerfectFourPlayerBinaryObservableStrategy
        query sign strategy :=
  operatorRefutation_excludes_perfectFourPlayerBinaryObservableStrategy
    query sign strategy
    (operatorRefutation_of_pref_of_primitiveCircuit_lifts
      query sign hlift hpref)

/--
If every primitive four-player incidence circuit lifts, every concrete
perfect commuting-observable strategy satisfies the MERP parity criterion.
-/
theorem
    perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity_of_primitiveCircuit_lifts
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    {Hilbert : Type*} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c)
    (hperfect :
      IsPerfectFourPlayerBinaryObservableStrategy query sign strategy) :
    IsMERPPerfectParity query sign := by
  by_contra hnotMERP
  have hpref : HasPREF query sign := by
    exact Classical.byContradiction fun hnopref =>
      hnotMERP
        ((isMERPPerfectParity_iff_not_hasPREF query sign).mpr hnopref)
  exact
    (pref_excludes_perfectFourPlayerBinaryObservableStrategy_of_primitiveCircuit_lifts
      query sign strategy hlift hpref) hperfect

/--
The concrete perfect-strategy conclusion with the finite and structural
parts exposed as the three possible primitive-support size ranges.
-/
theorem
    perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity_of_support_windows
    [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type*} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → FourByThreeClause)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy (Fin 3) Hilbert)
    (hsmall :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card ≤ 8 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hnine :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card = 9 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hten :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card = 10 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hperfect :
      IsPerfectFourPlayerBinaryObservableStrategy query sign strategy) :
    IsMERPPerfectParity query sign := by
  exact
    perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity_of_primitiveCircuit_lifts
      query sign strategy
      (primitiveCircuit_lifts_of_support_windows
        query hsmall hnine hten)
      hperfect

/-- For a distinct-clause four-player three-question binary XOR game, every
exact perfect finite-dimensional observable strategy satisfies the MERP
parity criterion. -/
theorem
    perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity
    [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type*} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → FourByThreeClause)
    (hquery : Function.Injective query)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy (Fin 3) Hilbert)
    (hperfect :
      IsPerfectFourPlayerBinaryObservableStrategy query sign strategy) :
    IsMERPPerfectParity query sign := by
  exact
    perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity_of_primitiveCircuit_lifts
      query sign strategy
      (primitiveCircuit_lifts_fourByThree query hquery)
      hperfect

/-- Therefore a non-MERP four-player three-question binary XOR game has no
exact perfect finite-dimensional observable strategy. -/
theorem nonMERP_excludes_perfectFourPlayerBinaryObservableStrategy
    [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type*} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → FourByThreeClause)
    (hquery : Function.Injective query)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy (Fin 3) Hilbert)
    (hnotMERP : ¬ IsMERPPerfectParity query sign) :
    ¬ IsPerfectFourPlayerBinaryObservableStrategy
        query sign strategy := by
  intro hperfect
  exact hnotMERP
    (perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity
      query hquery sign strategy hperfect)

end

end XORGame
end QIT

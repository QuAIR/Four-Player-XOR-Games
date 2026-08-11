/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.CircuitSupport
public import XORGameFormalization.SupportLift

/-!
# Reducing primitive four-by-three circuits to three finite support windows

The rank argument bounds every primitive incidence circuit by ten clauses.
This module packages that structural result in the form needed by the final
proof: exact lifts on supports of size at most eight, exactly nine, and
exactly ten suffice for every primitive circuit.  The three cardinality
cases therefore meet at one explicit mathematical interface.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- Exact balanced liftability after restricting to the nonzero support. -/
def HasSupportExactMultiplicityBalancedLift
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (c : E → ℤ) : Prop :=
  HasExactMultiplicityBalancedLift
    (restrictQueryToIntegerSupport query c)
    (fun clause : ↥(integerSupport c) => c clause.1)

/--
For one primitive circuit, the rank-ten support bound reduces liftability to
the three disjoint windows `≤ 8`, `= 9`, and `= 10`.
-/
theorem primitiveCircuit_balancedLift_of_support_windows
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (hsmall :
      (integerSupport c).card ≤ 8 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hnine :
      (integerSupport c).card = 9 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hten :
      (integerSupport c).card = 10 →
        HasSupportExactMultiplicityBalancedLift query c) :
    HasBalancedLift query c := by
  have hbound :
      (integerSupport c).card ≤ 10 :=
    primitiveIncidenceCircuit_support_card_le_ten query c hc
  have hwindow :
      (integerSupport c).card ≤ 8 ∨
        (integerSupport c).card = 9 ∨
        (integerSupport c).card = 10 := by
    omega
  rcases hwindow with hle | hcard | hcard
  · exact balancedLift_of_exactLift_on_integerSupport
      query c (hsmall hle)
  · exact balancedLift_of_exactLift_on_integerSupport
      query c (hnine hcard)
  · exact balancedLift_of_exactLift_on_integerSupport
      query c (hten hcard)

/--
Uniform lift theorems for the three support windows imply the primitive
circuit lifting hypothesis used by the operator-refutation assembly.
-/
theorem primitiveCircuit_lifts_of_support_windows
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause)
    (hsmall :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card ≤ 8 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hnine :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card = 9 →
        HasSupportExactMultiplicityBalancedLift query c)
    (hten :
      ∀ c : E → ℤ,
        IsPrimitiveKernelCircuit
            (incidenceRelationHom query) c →
        (integerSupport c).card = 10 →
        HasSupportExactMultiplicityBalancedLift query c) :
    ∀ c : E → ℤ,
      IsPrimitiveKernelCircuit
          (incidenceRelationHom query) c →
      HasBalancedLift query c := by
  intro c hc
  exact primitiveCircuit_balancedLift_of_support_windows
    query c hc
    (hsmall c hc)
    (hnine c hc)
    (hten c hc)

end

end XORGame
end QIT

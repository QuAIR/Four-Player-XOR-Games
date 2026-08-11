/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SafeHoleExcess
public import XORGameFormalization.SafePacking
public import XORGameFormalization.Lift

/-!
# Structural contradiction for the nine-clause boundary

This module packages the purely Hamming-geometric end of the nine-clause
argument.  If nonliftability forced every safe center to see the support in
even layers and forced distinct safe centers to be distance at least three,
then the safe-hole excess theorem gives at least thirteen centers, while the
layer-two/layer-four packing theorem permits at most six.

The matching-theoretic escape lemmas are exposed as the two implications
from nonliftability needed by this conditional structural theorem.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
The nine-clause boundary contradiction from the two structural consequences
of nonliftability: even support layers and distance-three separation.
-/
theorem nineClause_exactLift_of_nonliftable_even_separated
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (heven :
      ¬ HasExactMultiplicityBalancedLift query y →
      ∀ center ∈ safeCenters (Finset.univ.image query),
        ∀ clause ∈ Finset.univ.image query,
          Even (hammingDistance center clause))
    (hseparated :
      ¬ HasExactMultiplicityBalancedLift query y →
      ∀ ⦃u⦄, u ∈ safeCenters (Finset.univ.image query) →
        ∀ ⦃v⦄, v ∈ safeCenters (Finset.univ.image query) →
          u ≠ v → 3 ≤ hammingDistance u v) :
    HasExactMultiplicityBalancedLift query y := by
  by_contra hnotLift
  let support := Finset.univ.image query
  have heven' :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause) := by
    simpa [support] using heven hnotLift
  have hseparated' :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support →
          u ≠ v → 3 ≤ hammingDistance u v := by
    simpa [support] using hseparated hnotLift
  have hlower :
      13 ≤ (safeCenters support).card := by
    simpa [support] using
      nineClause_fullCircuit_separated_even_safeCenters_card_ge_thirteen
        query hquery hcard hCircuit
          (by simpa [support] using hseparated')
          (by simpa [support] using heven')
  have hsupportNonempty : support.Nonempty := by
    have hnonemptyE : Nonempty E := by
      rw [← Fintype.card_pos_iff]
      omega
    let clause : E := Classical.choice hnonemptyE
    exact ⟨query clause,
      Finset.mem_image.mpr
        ⟨clause, Finset.mem_univ clause, rfl⟩⟩
  have hupper :
      (safeCenters support).card ≤ 6 :=
    safeCenters_card_le_six_of_even_separated
      support hsupportNonempty hseparated' heven'
  omega

end

end XORGame
end QIT

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
# A uniform structural contradiction below nine clauses

For a nonempty support of at most eight clauses, separated even-distance
safe centers cannot exist.  The packing theorem gives at most six safe
centers, while the global safe-hole excess inequality would require

`0 ≤ 9 * |S| - 81 + |U| ≤ 72 - 81 + 6`.

Consequently every circuit in this cardinality range is discharged by one
general theorem; no finite classification is a premise of this structural
branch.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
No nonempty support of at most eight clauses can have mutually separated
safe centers whose cross-distances to the support are all even.
-/
theorem atMostEight_evenSeparated_safeCenters_impossible
    (support : Finset FourByThreeClause)
    (hsupport : support.Nonempty)
    (hcard : support.card ≤ 8)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support →
          u ≠ v → 3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    False := by
  have hsafeCard :
      (safeCenters support).card ≤ 6 :=
    safeCenters_card_le_six_of_even_separated
      support hsupport hseparated heven
  have hexcess :=
    safeHole_neighborhood_excess support
      hseparated heven
  have hsumNonnegative :
      (0 : ℤ) ≤
        ∑ center ∈ safeCenters support,
          ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
    apply Finset.sum_nonneg
    intro center hcenter
    have hlower := hexcess.1 center hcenter
    omega
  have hsupportCardInt :
      (support.card : ℤ) ≤ 8 := by
    exact_mod_cast hcard
  have hsafeCardInt :
      ((safeCenters support).card : ℤ) ≤ 6 := by
    exact_mod_cast hsafeCard
  nlinarith [hexcess.2]

/--
Query-indexed form: if nonliftability supplied the even-distance and
separation properties, a support of at most eight distinct clauses would
already be exactly liftable.
-/
theorem atMostEight_exactLift_of_nonliftable_even_separated
    {E : Type uE} [Fintype E] [Nonempty E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E ≤ 8)
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
  have hsupportNonempty : support.Nonempty := by
    let clause : E := Classical.choice (inferInstance : Nonempty E)
    exact ⟨query clause,
      Finset.mem_image.mpr
        ⟨clause, Finset.mem_univ clause, rfl⟩⟩
  have hsupportCard : support.card ≤ 8 := by
    change (Finset.univ.image query).card ≤ 8
    rw [Finset.card_image_of_injective Finset.univ hquery,
      Finset.card_univ]
    exact hcard
  exact atMostEight_evenSeparated_safeCenters_impossible
    support hsupportNonempty hsupportCard
      (by simpa [support] using hseparated hnotLift)
      (by simpa [support] using heven hnotLift)

end

end XORGame
end QIT

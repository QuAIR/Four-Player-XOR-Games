/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SafePacking
public import XORGameFormalization.TenNoncovering
public import XORGameFormalization.Lift

/-!
# Structural assembly for the ten-clause boundary

The covering branch is impossible by the connected-Gram theorem, hence a
ten-row full circuit has a safe center.  If nonliftability also forced even
support layers and distance-three separation, the universal packing bound
would give at most six safe centers.  The noncovering theorem then forces
the impossible inequality `12 ≤ 10`.

As at nine clauses, this module exposes the two matching-theoretic
consequences of nonliftability rather than hiding them behind a census.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- The row-wise safe-center witness as membership in the support safe set. -/
theorem tenClause_fullCircuit_safeCenters_nonempty
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 10)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    (safeCenters (Finset.univ.image query)).Nonempty := by
  have hnonemptyE : Nonempty E := by
    rw [← Fintype.card_pos_iff]
    omega
  letI : Nonempty E := hnonemptyE
  obtain ⟨center, hcenter⟩ :=
    tenClause_fullCircuit_has_safeCenter
      query hquery hcard hCircuit
  refine ⟨center, ?_⟩
  simp only [safeCenters, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro clause hclause
  obtain ⟨index, _hindex, rfl⟩ :=
    Finset.mem_image.mp hclause
  exact hcenter index

/--
Even support layers and separated safe centers, when forced by
nonliftability, close the ten-clause boundary structurally.
-/
theorem tenClause_exactLift_of_nonliftable_even_separated
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 10)
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
  have hsupportCard : support.card = 10 := by
    change (Finset.univ.image query).card = 10
    rw [Finset.card_image_of_injective Finset.univ hquery,
      Finset.card_univ]
    exact hcard
  have hsupportNonempty : support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hempty
    rw [hempty] at hsupportCard
    simp at hsupportCard
  have hsafeNonempty :
      (safeCenters support).Nonempty := by
    simpa [support] using
      tenClause_fullCircuit_safeCenters_nonempty
        query hquery hcard hCircuit
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
  have hsafeCard :
      (safeCenters support).card ≤ 6 :=
    safeCenters_card_le_six_of_even_separated
      support hsupportNonempty hseparated' heven'
  have hlayers :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          hammingDistance center clause = 2 ∨
            hammingDistance center clause = 4 := by
    intro center hcenter clause hclause
    exact safeCenter_support_distance_two_or_four
      support center clause hcenter hclause
        (heven' center hcenter clause hclause)
  exact tenClause_noncovering_geometry_impossible
    support hsupportCard hsafeNonempty hsafeCard
      hseparated' hlayers

end

end XORGame
end QIT

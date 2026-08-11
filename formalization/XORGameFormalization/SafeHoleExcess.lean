/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SafeCenter
public import XORGameFormalization.NineBall
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Safe-hole neighborhood excess

This module formalizes the safe-hole excess argument at the nine-clause
boundary.  The argument uses only Hamming-ball incidence counts: separated
safe holes have disjoint one-spheres, and even safe-hole-to-support distances
make each local coverage mass twice the number of layer-two support clauses.
-/

@[expose] public section

namespace QIT
namespace XORGame

open scoped BigOperators

universe uE

noncomputable section

/-- The open Hamming neighborhood of a safe hole. -/
def safeHoleNeighborhood (center : FourByThreeClause) :
    Finset FourByThreeClause :=
  hammingSphere center 1

/-- The number of support clauses at distance two from a specified center. -/
def safeHoleLayerTwoCount
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause) : Nat :=
  (support.filter fun clause => hammingDistance center clause = 2).card

private theorem support_distance_two_or_four_of_safe_even
    (support : Finset FourByThreeClause)
    (center clause : FourByThreeClause)
    (hcenterSafe : center ∈ safeCenters support)
    (hclause : clause ∈ support)
    (heven : Even (hammingDistance center clause)) :
    hammingDistance center clause = 2 ∨
      hammingDistance center clause = 4 := by
  have hlower :
      2 ≤ hammingDistance center clause :=
    (Finset.mem_filter.mp hcenterSafe).2 clause hclause
  have hupper := hammingDistance_le_four center clause
  obtain ⟨half, hhalf⟩ := heven
  omega

private theorem safeHoleNeighborhood_filter_eq_ball_inter
    (center clause : FourByThreeClause)
    (hfar : 2 ≤ hammingDistance center clause) :
    (safeHoleNeighborhood center).filter
        (fun point => hammingDistance point clause ≤ 1) =
      radiusOneBall center ∩ radiusOneBall clause := by
  ext point
  simp only [safeHoleNeighborhood, hammingSphere, radiusOneBall,
    closedHammingBall, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_inter]
  constructor
  · rintro ⟨hcenterPoint, hpointClause⟩
    exact ⟨by omega,
      by simpa only [hammingDistance_comm] using hpointClause⟩
  · rintro ⟨hcenterPoint, hclausePoint⟩
    have hcenterPointNeZero :
        hammingDistance center point ≠ 0 := by
      intro hzero
      have hpoint : center = point :=
        (hammingDistance_eq_zero_iff center point).mp hzero
      subst point
      rw [hammingDistance_comm] at hclausePoint
      omega
    exact ⟨by omega,
      by simpa only [hammingDistance_comm] using hclausePoint⟩

private theorem safeHoleNeighborhood_ball_slice_card
    (center clause : FourByThreeClause)
    (hdistance :
      hammingDistance center clause = 2 ∨
        hammingDistance center clause = 4) :
    ((safeHoleNeighborhood center).filter
        fun point => hammingDistance point clause ≤ 1).card =
      if hammingDistance center clause = 2 then 2 else 0 := by
  have hfar : 2 ≤ hammingDistance center clause := by
    rcases hdistance with htwo | hfour <;> omega
  rw [safeHoleNeighborhood_filter_eq_ball_inter center clause hfar]
  rcases hdistance with htwo | hfour
  · rw [if_pos htwo]
    exact radiusOneBall_inter_card_of_distance_two center clause htwo
  · rw [if_neg (by omega)]
    exact radiusOneBall_inter_card_of_three_le center clause (by omega)

/--
The coverage mass on the eight neighbors of an even-distance safe hole is
twice the number of support clauses at distance two from it.
-/
theorem safeHoleNeighborhood_coverageMass
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hcenterSafe : center ∈ safeCenters support)
    (heven :
      ∀ clause ∈ support,
        Even (hammingDistance center clause)) :
    (∑ point ∈ safeHoleNeighborhood center,
        coverageMultiplicity support point) =
      2 * safeHoleLayerTwoCount support center := by
  let covers : FourByThreeClause → FourByThreeClause → Prop :=
    fun clause point => hammingDistance point clause ≤ 1
  have hdouble :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      covers
      (s := support)
      (t := safeHoleNeighborhood center)
  have hdouble' :
      (∑ clause ∈ support,
          ((safeHoleNeighborhood center).filter
            fun point => covers clause point).card) =
        ∑ point ∈ safeHoleNeighborhood center,
          coverageMultiplicity support point := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow,
      coverageMultiplicity, covers] using hdouble
  rw [← hdouble']
  have hslice :
      ∀ clause ∈ support,
        ((safeHoleNeighborhood center).filter
          fun point => covers clause point).card =
          if hammingDistance center clause = 2 then 2 else 0 := by
    intro clause hclause
    exact safeHoleNeighborhood_ball_slice_card center clause
      (support_distance_two_or_four_of_safe_even
        support center clause hcenterSafe hclause
        (heven clause hclause))
  calc
    (∑ clause ∈ support,
        ((safeHoleNeighborhood center).filter
          fun point => covers clause point).card) =
        ∑ clause ∈ support,
          if hammingDistance center clause = 2 then 2 else 0 := by
      apply Finset.sum_congr rfl
      intro clause hclause
      exact hslice clause hclause
    _ = 2 * safeHoleLayerTwoCount support center := by
      have hcount :
          (∑ clause ∈ support,
              if hammingDistance center clause = 2 then 1 else 0) =
            safeHoleLayerTwoCount support center := by
        exact Finset.sum_boole
          (fun clause => hammingDistance center clause = 2) support
      simp_rw [show ∀ clause,
          (if hammingDistance center clause = 2 then 2 else 0) =
            2 * (if hammingDistance center clause = 2 then 1 else 0) by
        intro clause
        split <;> rfl]
      rw [← Finset.mul_sum, hcount]

private theorem coverageMultiplicity_pos_of_not_safe
    (support : Finset FourByThreeClause)
    (point : FourByThreeClause)
    (hpoint : point ∉ safeCenters support) :
    0 < coverageMultiplicity support point := by
  have hnotAll :
      ¬ ∀ clause ∈ support,
          2 ≤ hammingDistance point clause := by
    simpa [safeCenters] using hpoint
  push Not at hnotAll
  obtain ⟨clause, hclause, hnear⟩ := hnotAll
  rw [coverageMultiplicity]
  apply Finset.card_pos.mpr
  exact ⟨clause, Finset.mem_filter.mpr ⟨hclause, by omega⟩⟩

/--
Every neighbor of a safe hole is covered when distinct safe holes are
separated by distance at least three.
-/
theorem safeHoleNeighborhood_coverageMultiplicity_pos
    (support : Finset FourByThreeClause)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters support)
    (point : FourByThreeClause)
    (hpoint : point ∈ safeHoleNeighborhood center) :
    0 < coverageMultiplicity support point := by
  have hdistance :
      hammingDistance center point = 1 := by
    simpa [safeHoleNeighborhood, hammingSphere] using hpoint
  have hne : center ≠ point := by
    intro heq
    subst point
    simp at hdistance
  apply coverageMultiplicity_pos_of_not_safe support point
  intro hpointSafe
  have := hseparated hcenter hpointSafe hne
  omega

/--
The one-spheres around separated safe holes are pairwise disjoint.
-/
theorem safeHoleNeighborhood_pairwiseDisjoint
    (support : Finset FourByThreeClause)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v) :
    (safeCenters support : Set FourByThreeClause).PairwiseDisjoint
      safeHoleNeighborhood := by
  intro u hu v hv huv
  have hinterCard :
      (radiusOneBall u ∩ radiusOneBall v).card = 0 :=
    radiusOneBall_inter_card_of_three_le u v
      (hseparated hu hv huv)
  have hballs : Disjoint (radiusOneBall u) (radiusOneBall v) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Finset.card_eq_zero.mp hinterCard
  apply hballs.mono
  · intro point hpoint
    simp only [safeHoleNeighborhood, hammingSphere, radiusOneBall,
      closedHammingBall, Finset.mem_filter, Finset.mem_univ, true_and] at hpoint ⊢
    omega
  · intro point hpoint
    simp only [safeHoleNeighborhood, hammingSphere, radiusOneBall,
      closedHammingBall, Finset.mem_filter, Finset.mem_univ, true_and] at hpoint ⊢
    omega

/--
The excess on a safe hole's eight neighbors is `2 * (aᵤ - 4)`.
-/
theorem safeHoleNeighborhood_excess
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hcenterSafe : center ∈ safeCenters support)
    (heven :
      ∀ clause ∈ support,
        Even (hammingDistance center clause)) :
    (∑ point ∈ safeHoleNeighborhood center,
        ((coverageMultiplicity support point : ℤ) - 1)) =
      2 * ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
  have hmass :=
    safeHoleNeighborhood_coverageMass support center hcenterSafe heven
  have hmassInt :
      (∑ point ∈ safeHoleNeighborhood center,
          (coverageMultiplicity support point : ℤ)) =
        2 * (safeHoleLayerTwoCount support center : ℤ) := by
    exact_mod_cast hmass
  rw [Finset.sum_sub_distrib, hmassInt]
  simp [safeHoleNeighborhood]
  ring

/--
Separated safe holes with even cross-distances have at least four layer-two
support clauses apiece, and their total local excess is bounded by the global
radius-one-ball coverage excess.
-/
theorem safeHole_neighborhood_excess
    (support : Finset FourByThreeClause)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    (∀ center ∈ safeCenters support,
        4 ≤ safeHoleLayerTwoCount support center) ∧
      (2 : ℤ) *
          (∑ center ∈ safeCenters support,
            ((safeHoleLayerTwoCount support center : ℤ) - 4)) ≤
        9 * (support.card : ℤ) - 81 +
          ((safeCenters support).card : ℤ) := by
  let covered :=
    Finset.univ.filter fun point : FourByThreeClause =>
      0 < coverageMultiplicity support point
  have hcontained :
      ∀ center ∈ safeCenters support,
        safeHoleNeighborhood center ⊆ covered := by
    intro center hcenter point hpoint
    simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and]
    exact safeHoleNeighborhood_coverageMultiplicity_pos
      support hseparated center hcenter point hpoint
  have hcoveredPositive :
      ∀ point ∈ covered,
        1 ≤ coverageMultiplicity support point := by
    intro point hpoint
    simpa [covered] using hpoint
  have hlocalGlobal :=
    pairwiseDisjoint_neighborhood_excess_le_global
      (safeCenters support) covered safeHoleNeighborhood
      (coverageMultiplicity support)
      (safeHoleNeighborhood_pairwiseDisjoint support hseparated)
      hcontained hcoveredPositive
  constructor
  · intro center hcenter
    have hmass :=
      safeHoleNeighborhood_coverageMass support center hcenter
        (heven center hcenter)
    have hmassLower :
        (safeHoleNeighborhood center).card ≤
          ∑ point ∈ safeHoleNeighborhood center,
            coverageMultiplicity support point := by
      calc
        (safeHoleNeighborhood center).card =
            ∑ _point ∈ safeHoleNeighborhood center, 1 := by simp
        _ ≤
            ∑ point ∈ safeHoleNeighborhood center,
              coverageMultiplicity support point := by
          apply Finset.sum_le_sum
          intro point hpoint
          exact safeHoleNeighborhood_coverageMultiplicity_pos
            support hseparated center hcenter point hpoint
    have hneighborhoodCard :
        (safeHoleNeighborhood center).card = 8 := by
      simp [safeHoleNeighborhood]
    omega
  · calc
      (2 : ℤ) *
          (∑ center ∈ safeCenters support,
            ((safeHoleLayerTwoCount support center : ℤ) - 4)) =
          ∑ center ∈ safeCenters support,
            ∑ point ∈ safeHoleNeighborhood center,
              ((coverageMultiplicity support point : ℤ) - 1) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro center hcenter
        exact (safeHoleNeighborhood_excess support center hcenter
          (heven center hcenter)).symm
      _ ≤
          ∑ point ∈ covered,
            ((coverageMultiplicity support point : ℤ) - 1) :=
        hlocalGlobal
      _ =
          9 * (support.card : ℤ) - 81 +
            ((safeCenters support).card : ℤ) := by
        simpa [covered] using coverageExcess_identity support

/--
For nine support clauses, the safe-hole excess inequality simplifies to
`2 * Σᵤ (aᵤ - 4) ≤ |U|`.
-/
theorem nineClause_safeHole_excess
    (support : Finset FourByThreeClause)
    (hcard : support.card = 9)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    (∀ center ∈ safeCenters support,
        4 ≤ safeHoleLayerTwoCount support center) ∧
      (2 : ℤ) *
          (∑ center ∈ safeCenters support,
            ((safeHoleLayerTwoCount support center : ℤ) - 4)) ≤
        (safeCenters support).card := by
  have hgeneral :=
    safeHole_neighborhood_excess support hseparated heven
  constructor
  · exact hgeneral.1
  · simpa [hcard] using hgeneral.2

/--
A nonempty separated, even-distance safe-hole family for nine clauses
contains a center with exactly four layer-two support clauses.
-/
theorem nineClause_exists_exactFour_safeCenter
    (support : Finset FourByThreeClause)
    (hcard : support.card = 9)
    (hnonempty : (safeCenters support).Nonempty)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    ∃ center ∈ safeCenters support,
      safeHoleLayerTwoCount support center = 4 := by
  have hexcess :=
    nineClause_safeHole_excess support hcard hseparated heven
  by_contra hexact
  push Not at hexact
  have hsumLower :
      ((safeCenters support).card : ℤ) ≤
        ∑ center ∈ safeCenters support,
          ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
    calc
      ((safeCenters support).card : ℤ) =
          ∑ _center ∈ safeCenters support, (1 : ℤ) := by simp
      _ ≤
          ∑ center ∈ safeCenters support,
            ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
        apply Finset.sum_le_sum
        intro center hcenter
        have hlower := hexcess.1 center hcenter
        have hne := hexact center hcenter
        omega
  have hcardPositive :
      (0 : ℤ) < (safeCenters support).card := by
    exact_mod_cast Finset.card_pos.mpr hnonempty
  nlinarith [hexcess.2]

/--
Four layer-two clauses around an even-distance safe center force at least
thirteen safe centers.

No separation or labeled-cycle hypothesis on those four clauses is needed:
their four radius-one balls cover at most twelve of the 24 layer-two points.
The center itself is the thirteenth safe point.  Clauses outside the
layer-two filter are automatically in layer four.
-/
theorem fourLayerTwo_evenSafeCenter_safeCenters_card_ge_thirteen
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hcenterSafe : center ∈ safeCenters support)
    (heven :
      ∀ clause ∈ support,
        Even (hammingDistance center clause))
    (hlayerTwoCount :
      safeHoleLayerTwoCount support center = 4) :
    13 ≤ (safeCenters support).card := by
  let layerTwoClauses :=
    support.filter fun clause =>
      hammingDistance center clause = 2
  apply four_layerTwo_five_layerFour_safeCenters_card_ge_thirteen
    center support layerTwoClauses
  · simpa [layerTwoClauses, safeHoleLayerTwoCount] using hlayerTwoCount
  · intro clause hclause
    exact (Finset.mem_filter.mp hclause).2
  · intro clause hclause
    have hdistance :=
      support_distance_two_or_four_of_safe_even
        support center clause hcenterSafe hclause
          (heven clause hclause)
    rcases hdistance with htwo | hfour
    · exact Or.inl (Finset.mem_filter.mpr ⟨hclause, htwo⟩)
    · exact Or.inr hfour

/--
Nine clauses with a nonempty separated safe-hole set and even
safe-hole-to-support distances have at least thirteen safe centers.
-/
theorem nineClause_separated_even_safeCenters_card_ge_thirteen
    (support : Finset FourByThreeClause)
    (hcard : support.card = 9)
    (hnonempty : (safeCenters support).Nonempty)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    13 ≤ (safeCenters support).card := by
  obtain ⟨center, hcenter, hcount⟩ :=
    nineClause_exists_exactFour_safeCenter
      support hcard hnonempty hseparated heven
  exact fourLayerTwo_evenSafeCenter_safeCenters_card_ge_thirteen
    support center hcenter (heven center hcenter) hcount

/--
Direct nine-row circuit interface.  Full-circuit noncoverage supplies the
safe hole; only pairwise safe-hole separation and even cross-distances
remain as structural inputs.
-/
theorem nineClause_fullCircuit_separated_even_safeCenters_card_ge_thirteen
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters (Finset.univ.image query) →
        ∀ ⦃v⦄, v ∈ safeCenters (Finset.univ.image query) → u ≠ v →
          3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters (Finset.univ.image query),
        ∀ clause ∈ Finset.univ.image query,
          Even (hammingDistance center clause)) :
    13 ≤ (safeCenters (Finset.univ.image query)).card := by
  have hsupportCard :
      (Finset.univ.image query).card = 9 := by
    rw [Finset.card_image_of_injective Finset.univ hquery,
      Finset.card_univ]
    exact hcard
  obtain ⟨center, hcenterRows⟩ :=
    nineClause_fullCircuit_has_safeCenter query hcard hCircuit
  have hcenterSafe :
      center ∈ safeCenters (Finset.univ.image query) := by
    simp only [safeCenters, Finset.mem_filter, Finset.mem_univ, true_and]
    intro clause hclause
    obtain ⟨e, _he, rfl⟩ := Finset.mem_image.mp hclause
    exact hcenterRows e
  exact nineClause_separated_even_safeCenters_card_ge_thirteen
    (Finset.univ.image query) hsupportCard ⟨center, hcenterSafe⟩
      hseparated heven

end

end XORGame
end QIT

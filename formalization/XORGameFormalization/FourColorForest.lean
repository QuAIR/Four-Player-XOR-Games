/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.K4Trade
public import XORGameFormalization.ThreeColorForest
import Mathlib.Tactic

/-!
# Four-color selected-block forests

Balanced signatures of size at most two have a bipartite linear-forest
matching unless their pair imbalances form a nonzero `K₄` trade.  This is
the structural four-color obstruction used by the selected-block argument.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uN

noncomputable section

namespace ColorSignatureSystem

variable
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    (system : ColorSignatureSystem (Fin 4) Positive Negative)

def positiveSignatureCount (signature : Finset (Fin 4)) : Nat :=
  (Finset.univ.filter fun positive =>
    system.positiveSignature positive = signature).card

def negativeSignatureCount (signature : Finset (Fin 4)) : Nat :=
  (Finset.univ.filter fun negative =>
    system.negativeSignature negative = signature).card

def signatureImbalance (signature : Finset (Fin 4)) : ℤ :=
  (system.positiveSignatureCount signature : ℤ) -
    (system.negativeSignatureCount signature : ℤ)

def singletonImbalancesVanish : Prop :=
  ∀ color : Fin 4, system.signatureImbalance {color} = 0

def pairImbalanceWeights : K4EdgeWeights where
  edge01 := system.signatureImbalance {0, 1}
  edge02 := system.signatureImbalance {0, 2}
  edge03 := system.signatureImbalance {0, 3}
  edge12 := system.signatureImbalance {1, 2}
  edge13 := system.signatureImbalance {1, 3}
  edge23 := system.signatureImbalance {2, 3}

/-- The singleton and three pair signatures incident to one color. -/
def incidentSignatures (color : Fin 4) :
    Finset (Finset (Fin 4)) :=
  insert {color}
    (((Finset.univ : Finset (Fin 4)).erase color).image
      fun other => {color, other})

private theorem incidentSignatures_zero :
    incidentSignatures 0 =
      {{0}, {0, 1}, {0, 2}, {0, 3}} := by
  decide

private theorem incidentSignatures_one :
    incidentSignatures 1 =
      {{1}, {0, 1}, {1, 2}, {1, 3}} := by
  decide

private theorem incidentSignatures_two :
    incidentSignatures 2 =
      {{2}, {0, 2}, {1, 2}, {2, 3}} := by
  decide

private theorem incidentSignatures_three :
    incidentSignatures 3 =
      {{3}, {0, 3}, {1, 3}, {2, 3}} := by
  decide

private theorem sum_incidentSignatures_zero
    (f : Finset (Fin 4) → ℤ) :
    ∑ signature ∈ incidentSignatures 0, f signature =
      f {0} + f {0, 1} + f {0, 2} + f {0, 3} := by
  rw [incidentSignatures_zero]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp
  ring

private theorem sum_incidentSignatures_one
    (f : Finset (Fin 4) → ℤ) :
    ∑ signature ∈ incidentSignatures 1, f signature =
      f {1} + f {0, 1} + f {1, 2} + f {1, 3} := by
  rw [incidentSignatures_one]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp
  ring

private theorem sum_incidentSignatures_two
    (f : Finset (Fin 4) → ℤ) :
    ∑ signature ∈ incidentSignatures 2, f signature =
      f {2} + f {0, 2} + f {1, 2} + f {2, 3} := by
  rw [incidentSignatures_two]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp
  ring

private theorem sum_incidentSignatures_three
    (f : Finset (Fin 4) → ℤ) :
    ∑ signature ∈ incidentSignatures 3, f signature =
      f {3} + f {0, 3} + f {1, 3} + f {2, 3} := by
  rw [incidentSignatures_three]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  rw [Finset.sum_insert (by decide)]
  simp
  ring

private theorem signature_mem_incidentSignatures
    (color : Fin 4) (signature : Finset (Fin 4))
    (hcolor : color ∈ signature)
    (hcard : signature.card ≤ 2) :
    signature ∈ incidentSignatures color := by
  have hpositive : 0 < signature.card :=
    Finset.card_pos.mpr ⟨color, hcolor⟩
  have hcases :
      signature.card = 1 ∨ signature.card = 2 := by
    omega
  rcases hcases with hone | htwo
  · obtain ⟨only, rfl⟩ := Finset.card_eq_one.mp hone
    simp only [Finset.mem_singleton] at hcolor
    subst only
    exact Finset.mem_insert_self _ _
  · obtain ⟨left, right, hne, rfl⟩ :=
      Finset.card_eq_two.mp htwo
    simp only [Finset.mem_insert, Finset.mem_singleton] at hcolor
    rcases hcolor with hleft | hright
    · subst left
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨right,
        Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ right⟩,
          rfl⟩
    · subst right
      apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      exact ⟨left, by simp [hne], Finset.pair_comm _ _⟩

private theorem color_mem_of_mem_incidentSignatures
    (color : Fin 4) (signature : Finset (Fin 4))
    (hsignature : signature ∈ incidentSignatures color) :
    color ∈ signature := by
  rcases Finset.mem_insert.mp hsignature with rfl | hpair
  · simp
  · obtain ⟨other, _hother, rfl⟩ := Finset.mem_image.mp hpair
    simp

private theorem positiveEligible_card_eq_sum_signatureCounts
    (color : Fin 4) :
    (Finset.univ.filter fun positive : Positive =>
        color ∈ system.positiveSignature positive).card =
      ∑ signature ∈ incidentSignatures color,
        system.positiveSignatureCount signature := by
  let eligible :=
    Finset.univ.filter fun positive : Positive =>
      color ∈ system.positiveSignature positive
  have hmaps :
      Set.MapsTo system.positiveSignature
        eligible (incidentSignatures color) := by
    intro positive hpositive
    have hcolor :
        color ∈ system.positiveSignature positive :=
      (Finset.mem_filter.mp hpositive).2
    exact signature_mem_incidentSignatures color
      (system.positiveSignature positive) hcolor
        (system.positive_card_le_two positive)
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise hmaps
  change eligible.card =
    ∑ signature ∈ incidentSignatures color,
      system.positiveSignatureCount signature
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro signature hsignature
  have hcolor :=
    color_mem_of_mem_incidentSignatures color signature hsignature
  congr 1
  ext positive
  simp only [eligible,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro hsignatureEq
    exact ⟨by simpa [hsignatureEq] using hcolor, hsignatureEq⟩

private theorem negativeEligible_card_eq_sum_signatureCounts
    (color : Fin 4) :
    (Finset.univ.filter fun negative : Negative =>
        color ∈ system.negativeSignature negative).card =
      ∑ signature ∈ incidentSignatures color,
        system.negativeSignatureCount signature := by
  let eligible :=
    Finset.univ.filter fun negative : Negative =>
      color ∈ system.negativeSignature negative
  have hmaps :
      Set.MapsTo system.negativeSignature
        eligible (incidentSignatures color) := by
    intro negative hnegative
    have hcolor :
        color ∈ system.negativeSignature negative :=
      (Finset.mem_filter.mp hnegative).2
    exact signature_mem_incidentSignatures color
      (system.negativeSignature negative) hcolor
        (system.negative_card_le_two negative)
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise hmaps
  change eligible.card =
    ∑ signature ∈ incidentSignatures color,
      system.negativeSignatureCount signature
  rw [hpartition]
  apply Finset.sum_congr rfl
  intro signature hsignature
  have hcolor :=
    color_mem_of_mem_incidentSignatures color signature hsignature
  congr 1
  ext negative
  simp only [eligible,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · exact And.right
  · intro hsignatureEq
    exact ⟨by simpa [hsignatureEq] using hcolor, hsignatureEq⟩

def HasFourColorBalanceEquations : Prop :=
  system.signatureImbalance {0} +
        system.pairImbalanceWeights.edge01 +
        system.pairImbalanceWeights.edge02 +
        system.pairImbalanceWeights.edge03 = 0 ∧
    system.signatureImbalance {1} +
        system.pairImbalanceWeights.edge01 +
        system.pairImbalanceWeights.edge12 +
        system.pairImbalanceWeights.edge13 = 0 ∧
    system.signatureImbalance {2} +
        system.pairImbalanceWeights.edge02 +
        system.pairImbalanceWeights.edge12 +
        system.pairImbalanceWeights.edge23 = 0 ∧
    system.signatureImbalance {3} +
        system.pairImbalanceWeights.edge03 +
        system.pairImbalanceWeights.edge13 +
        system.pairImbalanceWeights.edge23 = 0

theorem hasFourColorBalanceEquations :
    system.HasFourColorBalanceEquations := by
  have hzero := congrArg (fun count : Nat => (count : ℤ))
    (system.balanced 0)
  have hone := congrArg (fun count : Nat => (count : ℤ))
    (system.balanced 1)
  have htwo := congrArg (fun count : Nat => (count : ℤ))
    (system.balanced 2)
  have hthree := congrArg (fun count : Nat => (count : ℤ))
    (system.balanced 3)
  rw [system.positiveEligible_card_eq_sum_signatureCounts,
    system.negativeEligible_card_eq_sum_signatureCounts] at hzero hone htwo hthree
  simp only [Nat.cast_sum] at hzero hone htwo hthree
  simp_rw [sum_incidentSignatures_zero] at hzero
  simp_rw [sum_incidentSignatures_one] at hone
  simp_rw [sum_incidentSignatures_two] at htwo
  simp_rw [sum_incidentSignatures_three] at hthree
  unfold HasFourColorBalanceEquations
  simp only [pairImbalanceWeights, signatureImbalance]
  exact ⟨by linear_combination hzero,
    by linear_combination hone,
    by linear_combination htwo,
    by linear_combination hthree⟩

theorem pairImbalance_isUnsignedKernel
    (hsingleton : system.singletonImbalancesVanish)
    (hbalance : system.HasFourColorBalanceEquations) :
    system.pairImbalanceWeights.IsUnsignedKernel := by
  rcases hbalance with ⟨hzero, hone, htwo, hthree⟩
  rw [hsingleton 0] at hzero
  rw [hsingleton 1] at hone
  rw [hsingleton 2] at htwo
  rw [hsingleton 3] at hthree
  exact ⟨by omega, by omega, by omega, by omega⟩

theorem k4Trade_of_singleton_zero
    (hsingleton : system.singletonImbalancesVanish)
    (hbalance : system.HasFourColorBalanceEquations) :
    ∃ x y : ℤ,
      system.pairImbalanceWeights = K4EdgeWeights.trade x y :=
  K4EdgeWeights.eq_trade_of_isUnsignedKernel
    system.pairImbalanceWeights
      (system.pairImbalance_isUnsignedKernel hsingleton hbalance)

abbrev PositiveActive :=
  {positive : Positive //
    (system.positiveSignature positive).Nonempty}

abbrev NegativeActive :=
  {negative : Negative //
    (system.negativeSignature negative).Nonempty}

private def positiveActiveFiberEquiv
    (signature : Finset (Fin 4))
    (hsignature : signature.Nonempty) :
    {positive : system.PositiveActive //
      system.positiveSignature positive.1 = signature} ≃
      {positive : Positive //
        system.positiveSignature positive = signature} where
  toFun positive := ⟨positive.1.1, positive.2⟩
  invFun positive :=
    ⟨⟨positive.1, by simpa [positive.2] using hsignature⟩,
      positive.2⟩
  left_inv positive := rfl
  right_inv positive := rfl

private def negativeActiveFiberEquiv
    (signature : Finset (Fin 4))
    (hsignature : signature.Nonempty) :
    {negative : system.NegativeActive //
      system.negativeSignature negative.1 = signature} ≃
      {negative : Negative //
        system.negativeSignature negative = signature} where
  toFun negative := ⟨negative.1.1, negative.2⟩
  invFun negative :=
    ⟨⟨negative.1, by simpa [negative.2] using hsignature⟩,
      negative.2⟩
  left_inv negative := rfl
  right_inv negative := rfl

theorem signatureImbalance_eq_zero_iff
    (signature : Finset (Fin 4)) :
    system.signatureImbalance signature = 0 ↔
      system.positiveSignatureCount signature =
        system.negativeSignatureCount signature := by
  unfold signatureImbalance
  omega

/--
If an exact signature has zero signed imbalance and occurs on at least one
side, then it has both a positive and a negative occurrence.
-/
theorem exists_positive_and_negative_of_signatureImbalance_zero
    (signature : Finset (Fin 4))
    (hzero : system.signatureImbalance signature = 0)
    (hoccurs :
      (∃ positive,
          system.positiveSignature positive = signature) ∨
        ∃ negative,
          system.negativeSignature negative = signature) :
    ∃ positive negative,
      system.positiveSignature positive = signature ∧
        system.negativeSignature negative = signature := by
  have hcounts :=
    (system.signatureImbalance_eq_zero_iff signature).mp hzero
  rcases hoccurs with hpositive | hnegative
  · obtain ⟨positive, hpositive⟩ := hpositive
    have hpositiveCount :
        0 < system.positiveSignatureCount signature := by
      unfold positiveSignatureCount
      apply Finset.card_pos.mpr
      exact ⟨positive, by simp [hpositive]⟩
    have hnegativeCount :
        0 < system.negativeSignatureCount signature := by
      omega
    obtain ⟨negative, hnegative⟩ :=
      Finset.card_pos.mp hnegativeCount
    exact ⟨positive, negative, hpositive,
      (Finset.mem_filter.mp hnegative).2⟩
  · obtain ⟨negative, hnegative⟩ := hnegative
    have hnegativeCount :
        0 < system.negativeSignatureCount signature := by
      unfold negativeSignatureCount
      apply Finset.card_pos.mpr
      exact ⟨negative, by simp [hnegative]⟩
    have hpositiveCount :
        0 < system.positiveSignatureCount signature := by
      omega
    obtain ⟨positive, hpositive⟩ :=
      Finset.card_pos.mp hpositiveCount
    exact ⟨positive, negative,
      (Finset.mem_filter.mp hpositive).2, hnegative⟩

private theorem activeFiber_card_eq
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0)
    (signature : Finset (Fin 4)) :
    Fintype.card
        {positive : system.PositiveActive //
          system.positiveSignature positive.1 = signature} =
      Fintype.card
        {negative : system.NegativeActive //
          system.negativeSignature negative.1 = signature} := by
  by_cases hsignature : signature.Nonempty
  · rw [Fintype.card_congr
        (system.positiveActiveFiberEquiv signature hsignature),
      Fintype.card_congr
        (system.negativeActiveFiberEquiv signature hsignature)]
    simpa [positiveSignatureCount, negativeSignatureCount,
      Fintype.card_subtype] using
        (system.signatureImbalance_eq_zero_iff signature).mp
          (hbalanced signature hsignature)
  · have hempty : signature = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hsignature
    subst signature
    letI : IsEmpty
        {positive : system.PositiveActive //
          system.positiveSignature positive.1 = ∅} :=
      ⟨fun positive => by
        simpa [positive.2] using positive.1.2⟩
    letI : IsEmpty
        {negative : system.NegativeActive //
          system.negativeSignature negative.1 = ∅} :=
      ⟨fun negative => by
        simpa [negative.2] using negative.1.2⟩
    simp

private noncomputable def equalActiveSignatureEquiv
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0) :
    system.PositiveActive ≃ system.NegativeActive :=
  Equiv.ofFiberEquiv
    (f := fun positive : system.PositiveActive =>
      system.positiveSignature positive.1)
    (g := fun negative : system.NegativeActive =>
      system.negativeSignature negative.1)
    (fun signature =>
      Fintype.equivOfCardEq
        (system.activeFiber_card_eq hbalanced signature))

private theorem equalActiveSignatureEquiv_preserves
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0)
    (positive : system.PositiveActive) :
    system.negativeSignature
        ((system.equalActiveSignatureEquiv hbalanced positive).1) =
      system.positiveSignature positive.1 := by
  simpa [equalActiveSignatureEquiv] using
    (Equiv.ofFiberEquiv_map
      (fun signature =>
        Fintype.equivOfCardEq
          (system.activeFiber_card_eq hbalanced signature))
      positive)

def HasLinearForestMatching : Prop :=
  ∃ matching : ColorwiseMatching system,
    matching.IsBipartiteLinearForest

private noncomputable def equalSignatureMatching
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0) :
    ColorwiseMatching system where
  Match color positive negative :=
    ∃ hcolor : color ∈ system.positiveSignature positive,
      negative =
        (system.equalActiveSignatureEquiv hbalanced
          ⟨positive, ⟨color, hcolor⟩⟩).1
  match_mem := by
    intro color positive negative hmatch
    rcases hmatch with ⟨hcolor, rfl⟩
    refine ⟨hcolor, ?_⟩
    have hpreserves :=
      system.equalActiveSignatureEquiv_preserves hbalanced
        ⟨positive, ⟨color, hcolor⟩⟩
    rw [hpreserves]
    exact hcolor
  positive_unique := by
    intro color positive hcolor
    let positiveActive : system.PositiveActive :=
      ⟨positive, ⟨color, hcolor⟩⟩
    refine ⟨(system.equalActiveSignatureEquiv
      hbalanced positiveActive).1, ?_, ?_⟩
    · exact ⟨hcolor, rfl⟩
    · intro negative hnegative
      rcases hnegative with ⟨hcolor', rfl⟩
      congr 2
  negative_unique := by
    intro color negative hcolor
    let equivalence :=
      system.equalActiveSignatureEquiv hbalanced
    let negativeActive : system.NegativeActive :=
      ⟨negative, ⟨color, hcolor⟩⟩
    let positiveActive : system.PositiveActive :=
      equivalence.symm negativeActive
    have hpreserves :
        system.negativeSignature
            (equivalence positiveActive).1 =
          system.positiveSignature positiveActive.1 :=
      system.equalActiveSignatureEquiv_preserves
        hbalanced positiveActive
    have hcolorPositive :
        color ∈ system.positiveSignature positiveActive.1 := by
      rw [← hpreserves]
      have happly :
          equivalence positiveActive = negativeActive :=
        equivalence.apply_symm_apply negativeActive
      rw [happly]
      exact hcolor
    refine ⟨positiveActive.1, ?_, ?_⟩
    · refine ⟨hcolorPositive, ?_⟩
      have happly :
          equivalence positiveActive = negativeActive :=
        equivalence.apply_symm_apply negativeActive
      exact (congrArg Subtype.val happly).symm
    · intro other hother
      rcases hother with ⟨hotherColor, hotherPartner⟩
      let otherActive : system.PositiveActive :=
        ⟨other, ⟨color, hotherColor⟩⟩
      have himages :
          equivalence otherActive = equivalence positiveActive := by
        apply Subtype.ext
        rw [← hotherPartner]
        exact congrArg Subtype.val
          (equivalence.apply_symm_apply negativeActive).symm
      have hactive : otherActive = positiveActive :=
        equivalence.injective himages
      exact congrArg Subtype.val hactive

private theorem equalSignatureMatching_adj_unique
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0)
    (vertex left right : Positive ⊕ Negative)
    (hleft :
      (system.equalSignatureMatching hbalanced).simpleGraph.Adj
        vertex left)
    (hright :
      (system.equalSignatureMatching hbalanced).simpleGraph.Adj
        vertex right) :
    left = right := by
  let equivalence :=
    system.equalActiveSignatureEquiv hbalanced
  cases vertex with
  | inl positive =>
      cases left with
      | inl leftPositive =>
          exact False.elim
            ((system.equalSignatureMatching hbalanced).simpleGraph_not_adj_inl_inl
              positive leftPositive hleft)
      | inr leftNegative =>
          cases right with
          | inl rightPositive =>
              exact False.elim
                ((system.equalSignatureMatching hbalanced).simpleGraph_not_adj_inl_inl
                  positive rightPositive hright)
          | inr rightNegative =>
              obtain ⟨leftColor, hleftMatch⟩ :=
                ((system.equalSignatureMatching hbalanced).simpleGraph_adj_inl_inr
                  positive leftNegative).mp hleft
              obtain ⟨rightColor, hrightMatch⟩ :=
                ((system.equalSignatureMatching hbalanced).simpleGraph_adj_inl_inr
                  positive rightNegative).mp hright
              rcases hleftMatch with ⟨hleftColor, rfl⟩
              rcases hrightMatch with ⟨hrightColor, rfl⟩
              congr 2
  | inr negative =>
      cases left with
      | inl leftPositive =>
          cases right with
          | inl rightPositive =>
              obtain ⟨leftColor, hleftMatch⟩ :=
                ((system.equalSignatureMatching hbalanced).simpleGraph_adj_inl_inr
                  leftPositive negative).mp hleft.symm
              obtain ⟨rightColor, hrightMatch⟩ :=
                ((system.equalSignatureMatching hbalanced).simpleGraph_adj_inl_inr
                  rightPositive negative).mp hright.symm
              rcases hleftMatch with ⟨hleftColor, hleftPartner⟩
              rcases hrightMatch with ⟨hrightColor, hrightPartner⟩
              let leftActive : system.PositiveActive :=
                ⟨leftPositive, ⟨leftColor, hleftColor⟩⟩
              let rightActive : system.PositiveActive :=
                ⟨rightPositive, ⟨rightColor, hrightColor⟩⟩
              have himages :
                  equivalence leftActive = equivalence rightActive := by
                apply Subtype.ext
                rw [← hleftPartner, ← hrightPartner]
              have hactive : leftActive = rightActive :=
                equivalence.injective himages
              exact congrArg (fun active => Sum.inl active.1) hactive
          | inr rightNegative =>
              exact False.elim
                ((system.equalSignatureMatching hbalanced).simpleGraph_not_adj_inr_inr
                  negative rightNegative hright)
      | inr leftNegative =>
          exact False.elim
            ((system.equalSignatureMatching hbalanced).simpleGraph_not_adj_inr_inr
              negative leftNegative hleft)

private theorem isAcyclic_of_adj_unique
    {Vertex : Type*} (graph : SimpleGraph Vertex)
    (hadjUnique :
      ∀ vertex left right,
        graph.Adj vertex left → graph.Adj vertex right →
          left = right) :
    graph.IsAcyclic := by
  intro vertex cycle hcycle
  have hfirst := cycle.adj_snd hcycle.not_nil
  have hlast := (cycle.adj_penultimate hcycle.not_nil).symm
  exact hcycle.snd_ne_penultimate
    (hadjUnique vertex cycle.snd cycle.penultimate hfirst hlast)

theorem linearForestMatching_of_nonemptySignature_balanced
    (hbalanced :
      ∀ signature : Finset (Fin 4), signature.Nonempty →
        system.signatureImbalance signature = 0) :
    system.HasLinearForestMatching := by
  let matching :=
    system.equalSignatureMatching hbalanced
  refine ⟨matching,
    matching.isBipartiteLinearForest_of_isAcyclic ?_⟩
  exact isAcyclic_of_adj_unique matching.simpleGraph
    (system.equalSignatureMatching_adj_unique hbalanced)

/-- Restrict a four-color signature system to the three colors different
from `removed`. -/
def restrictAwayColor (removed : Fin 4) :
    ColorSignatureSystem {color : Fin 4 // color ≠ removed}
      Positive Negative where
  positiveSignature positive :=
    Finset.univ.filter fun color =>
      color.1 ∈ system.positiveSignature positive
  negativeSignature negative :=
    Finset.univ.filter fun color =>
      color.1 ∈ system.negativeSignature negative
  positive_card_le_two positive := by
    refine (Finset.card_le_card_of_injOn Subtype.val ?_ ?_).trans
      (system.positive_card_le_two positive)
    · intro color hcolor
      exact (Finset.mem_filter.mp hcolor).2
    · intro left _ right _ heq
      exact Subtype.ext heq
  negative_card_le_two negative := by
    refine (Finset.card_le_card_of_injOn Subtype.val ?_ ?_).trans
      (system.negative_card_le_two negative)
    · intro color hcolor
      exact (Finset.mem_filter.mp hcolor).2
    · intro left _ right _ heq
      exact Subtype.ext heq
  balanced color := by
    simpa using system.balanced color.1

/-- Lift a matching on the three remaining colors when the removed color is
unused by every vertex. -/
noncomputable def liftRestrictAwayColorMatching
    (removed : Fin 4)
    (hpositive : ∀ positive,
      removed ∉ system.positiveSignature positive)
    (hnegative : ∀ negative,
      removed ∉ system.negativeSignature negative)
    (matching : ColorwiseMatching (system.restrictAwayColor removed)) :
    ColorwiseMatching system where
  Match color positive negative :=
    ∃ hcolor : color ≠ removed,
      matching.Match ⟨color, hcolor⟩ positive negative
  match_mem := by
    rintro color positive negative ⟨hcolor, hmatch⟩
    have hmem := matching.match_mem hmatch
    simpa [restrictAwayColor] using hmem
  positive_unique := by
    intro color positive hcolor
    have hne : color ≠ removed := by
      intro heq
      subst color
      exact hpositive positive hcolor
    have hreduced :
        (⟨color, hne⟩ : {other : Fin 4 // other ≠ removed}) ∈
          (system.restrictAwayColor removed).positiveSignature positive := by
      simp [restrictAwayColor, hcolor]
    obtain ⟨negative, hmatch, hunique⟩ :=
      matching.positive_unique ⟨color, hne⟩ positive hreduced
    refine ⟨negative, ⟨hne, hmatch⟩, ?_⟩
    intro other hother
    obtain ⟨hother, hotherMatch⟩ := hother
    have hsubtype :
        (⟨color, hother⟩ : {other : Fin 4 // other ≠ removed}) =
          ⟨color, hne⟩ := by
      rfl
    exact hunique other (by simpa [hsubtype] using hotherMatch)
  negative_unique := by
    intro color negative hcolor
    have hne : color ≠ removed := by
      intro heq
      subst color
      exact hnegative negative hcolor
    have hreduced :
        (⟨color, hne⟩ : {other : Fin 4 // other ≠ removed}) ∈
          (system.restrictAwayColor removed).negativeSignature negative := by
      simp [restrictAwayColor, hcolor]
    obtain ⟨positive, hmatch, hunique⟩ :=
      matching.negative_unique ⟨color, hne⟩ negative hreduced
    refine ⟨positive, ⟨hne, hmatch⟩, ?_⟩
    intro other hother
    obtain ⟨hother, hotherMatch⟩ := hother
    have hsubtype :
        (⟨color, hother⟩ : {other : Fin 4 // other ≠ removed}) =
          ⟨color, hne⟩ := by
      rfl
    exact hunique other (by simpa [hsubtype] using hotherMatch)

private theorem liftRestrictAwayColor_simpleGraph
    (removed : Fin 4)
    (hpositive : ∀ positive,
      removed ∉ system.positiveSignature positive)
    (hnegative : ∀ negative,
      removed ∉ system.negativeSignature negative)
    (matching : ColorwiseMatching (system.restrictAwayColor removed)) :
    (system.liftRestrictAwayColorMatching
      removed hpositive hnegative matching).simpleGraph =
      matching.simpleGraph := by
  ext left right
  cases left <;> cases right <;>
    simp only [ColorwiseMatching.simpleGraph,
      liftRestrictAwayColorMatching]
  all_goals
    constructor
    · rintro ⟨color, hcolor, hmatch⟩
      exact ⟨⟨color, hcolor⟩, hmatch⟩
    · rintro ⟨color, hmatch⟩
      exact ⟨color.1, color.2, hmatch⟩

/-- If one of the four colors is unused, the three-color forest theorem
applies to the remaining signatures. -/
theorem linearForestMatching_of_unusedColor
    (removed : Fin 4)
    (hpositive : ∀ positive,
      removed ∉ system.positiveSignature positive)
    (hnegative : ∀ negative,
      removed ∉ system.negativeSignature negative) :
    system.HasLinearForestMatching := by
  have hcard :
      Fintype.card {color : Fin 4 // color ≠ removed} ≤ 3 := by
    fin_cases removed <;> decide
  obtain ⟨matching, hforest⟩ :=
    threeColor_colorwiseMatching_linearForest
      (system.restrictAwayColor removed) hcard
  let lifted :=
    system.liftRestrictAwayColorMatching
      removed hpositive hnegative matching
  refine ⟨lifted, ?_⟩
  have hgraph : lifted.simpleGraph = matching.simpleGraph :=
    system.liftRestrictAwayColor_simpleGraph
      removed hpositive hnegative matching
  exact lifted.isBipartiteLinearForest_of_isAcyclic <| by
    rw [hgraph]
    exact hforest.1

private theorem signature_sdiff_singleton_card_eq_one
    {signature : Finset (Fin 4)} {color : Fin 4}
    (hcolor : color ∈ signature)
    (hcard : signature.card ≤ 2)
    (hne : signature ≠ {color}) :
    (signature \ {color}).card = 1 := by
  have hpositive : 0 < signature.card :=
    Finset.card_pos.mpr ⟨color, hcolor⟩
  have hnotOne : signature.card ≠ 1 := by
    intro hone
    obtain ⟨only, hsignature⟩ := Finset.card_eq_one.mp hone
    have honly : only = color := by
      symm
      simpa [hsignature] using hcolor
    exact hne (by simpa [honly] using hsignature)
  have htwo : signature.card = 2 := by omega
  rw [Finset.sdiff_singleton_eq_erase,
    Finset.card_erase_of_mem hcolor, htwo]

private theorem restore_positiveSingleton_forest
    (positive : Positive) (negative : Negative) (color : Fin 4)
    (hpositiveExact : system.positiveSignature positive = {color})
    (hnegativeColor : color ∈ system.negativeSignature negative)
    (hreduced :
      (system.eraseEndpointColors positive negative {color}
        (by simpa [hpositiveExact])
        (by simpa using hnegativeColor)).HasLinearForestMatching) :
    system.HasLinearForestMatching := by
  let hpositive :
      ({color} : Finset (Fin 4)) ⊆
        system.positiveSignature positive := by
    simpa [hpositiveExact]
  let hnegative :
      ({color} : Finset (Fin 4)) ⊆
        system.negativeSignature negative := by
    simpa using hnegativeColor
  change
    (system.eraseEndpointColors positive negative {color}
      hpositive hnegative).HasLinearForestMatching at hreduced
  obtain ⟨matching, hforest⟩ := hreduced
  let restored :=
    ColorwiseMatching.restoreEndpointColors system positive negative
      {color} hpositive hnegative matching
  refine ⟨restored,
    restored.isBipartiteLinearForest_of_isAcyclic ?_⟩
  exact
    ColorwiseMatching.restoreEndpointColors_isAcyclic_of_positive_exact
      system positive negative {color} hpositive hnegative
      hpositiveExact (by simp) matching hforest.1

private theorem restore_negativeSingleton_forest
    (positive : Positive) (negative : Negative) (color : Fin 4)
    (hpositiveColor : color ∈ system.positiveSignature positive)
    (hnegativeExact : system.negativeSignature negative = {color})
    (hreduced :
      (system.eraseEndpointColors positive negative {color}
        (by simpa using hpositiveColor)
        (by simpa [hnegativeExact])).HasLinearForestMatching) :
    system.HasLinearForestMatching := by
  let hpositive :
      ({color} : Finset (Fin 4)) ⊆
        system.positiveSignature positive := by
    simpa using hpositiveColor
  let hnegative :
      ({color} : Finset (Fin 4)) ⊆
        system.negativeSignature negative := by
    simpa [hnegativeExact]
  change
    (system.eraseEndpointColors positive negative {color}
      hpositive hnegative).HasLinearForestMatching at hreduced
  obtain ⟨matching, hforest⟩ := hreduced
  let restored :=
    ColorwiseMatching.restoreEndpointColors system positive negative
      {color} hpositive hnegative matching
  refine ⟨restored,
    restored.isBipartiteLinearForest_of_isAcyclic ?_⟩
  exact
    ColorwiseMatching.restoreEndpointColors_isAcyclic_of_negative_exact
      system positive negative {color} hpositive hnegative
      hnegativeExact (by simp) matching hforest.1

/-- Four-color singleton escape.

Delete the singleton color together with one opposite endpoint.  If that
endpoint had a two-color signature, it becomes a new singleton and the
construction recurses.  If both deleted endpoints were singleton and no
singleton remains, balance forces the deleted color to be unused, reducing
the residual problem to the three-color forest theorem. -/
theorem linearForestMatching_of_singleton
    (target : ColorSignatureSystem (Fin 4) Positive Negative)
    (hsingleton :
      (∃ positive color,
          target.positiveSignature positive = {color}) ∨
        ∃ negative color,
          target.negativeSignature negative = {color}) :
    target.HasLinearForestMatching := by
  classical
  let system := target
  change
    ((∃ positive color,
        system.positiveSignature positive = {color}) ∨
      ∃ negative color,
        system.negativeSignature negative = {color}) at hsingleton
  change system.HasLinearForestMatching
  rcases hsingleton with
    ⟨positive, color, hpositiveExact⟩ |
      ⟨negative, color, hnegativeExact⟩
  · have hpositiveColor :
        color ∈ system.positiveSignature positive := by
      simp [hpositiveExact]
    by_cases hpair :
        ∃ negative,
          color ∈ system.negativeSignature negative ∧
            system.negativeSignature negative ≠ {color}
    · obtain ⟨negative, hnegativeColor, hnegativeNe⟩ := hpair
      let hpositive :
          ({color} : Finset (Fin 4)) ⊆
            system.positiveSignature positive := by
        simpa [hpositiveExact]
      let hnegative :
          ({color} : Finset (Fin 4)) ⊆
            system.negativeSignature negative := by
        simpa using hnegativeColor
      let reduced :=
        system.eraseEndpointColors positive negative {color}
          hpositive hnegative
      have hcard :
          (system.negativeSignature negative \ {color}).card = 1 :=
        signature_sdiff_singleton_card_eq_one hnegativeColor
          (system.negative_card_le_two negative) hnegativeNe
      obtain ⟨nextColor, hnext⟩ := Finset.card_eq_one.mp hcard
      have hnextReduced :
          reduced.negativeSignature negative = {nextColor} := by
        simpa [reduced] using hnext
      have hreduced : reduced.HasLinearForestMatching :=
        linearForestMatching_of_singleton reduced
          (Or.inr ⟨negative, nextColor, hnextReduced⟩)
      exact system.restore_positiveSingleton_forest positive negative color
        hpositiveExact hnegativeColor (by simpa [reduced] using hreduced)
    · obtain ⟨negative, hnegativeColor⟩ :=
        system.exists_negative_of_positive_mem hpositiveColor
      have hnegativeExact :
          system.negativeSignature negative = {color} := by
        by_contra hne
        exact hpair ⟨negative, hnegativeColor, hne⟩
      let hpositive :
          ({color} : Finset (Fin 4)) ⊆
            system.positiveSignature positive := by
        simpa [hpositiveExact]
      let hnegative :
          ({color} : Finset (Fin 4)) ⊆
            system.negativeSignature negative := by
        simpa [hnegativeExact]
      let reduced :=
        system.eraseEndpointColors positive negative {color}
          hpositive hnegative
      by_cases hnext :
          (∃ other nextColor,
              reduced.positiveSignature other = {nextColor}) ∨
            ∃ other nextColor,
              reduced.negativeSignature other = {nextColor}
      · have hreduced :=
          linearForestMatching_of_singleton reduced hnext
        exact system.restore_positiveSingleton_forest positive negative color
          hpositiveExact hnegativeColor (by simpa [reduced] using hreduced)
      · have hnegativeUnused :
            ∀ other, color ∉ reduced.negativeSignature other := by
          intro other hcolor
          by_cases hother : other = negative
          · subst other
            rw [ColorSignatureSystem.eraseEndpointColors_negative_at,
              hnegativeExact] at hcolor
            simp at hcolor
          · have horiginal :
                color ∈ system.negativeSignature other :=
              system.eraseEndpointColors_negative_subset
                positive negative {color} hpositive hnegative other hcolor
            have hexact :
                system.negativeSignature other = {color} := by
              by_contra hne
              exact hpair ⟨other, horiginal, hne⟩
            apply hnext
            right
            refine ⟨other, color, ?_⟩
            simp [reduced, ColorSignatureSystem.eraseEndpointColors,
              hother, hexact]
        have hpositiveUnused :
            ∀ other, color ∉ reduced.positiveSignature other := by
          have hnegativeFilter :
              Finset.univ.filter
                  (fun other =>
                    color ∈ reduced.negativeSignature other) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro other _
            exact hnegativeUnused other
          have hpositiveCard :
              (Finset.univ.filter
                (fun other =>
                  color ∈ reduced.positiveSignature other)).card = 0 := by
            rw [reduced.balanced color, hnegativeFilter]
            simp
          intro other hcolor
          have hmem :
              other ∈ Finset.univ.filter
                (fun vertex =>
                  color ∈ reduced.positiveSignature vertex) := by
            simp [hcolor]
          have := Finset.card_pos.mpr ⟨other, hmem⟩
          omega
        have hreduced := reduced.linearForestMatching_of_unusedColor
          color hpositiveUnused hnegativeUnused
        exact system.restore_positiveSingleton_forest positive negative color
          hpositiveExact hnegativeColor (by simpa [reduced] using hreduced)
  · have hnegativeColor :
        color ∈ system.negativeSignature negative := by
      simp [hnegativeExact]
    by_cases hpair :
        ∃ positive,
          color ∈ system.positiveSignature positive ∧
            system.positiveSignature positive ≠ {color}
    · obtain ⟨positive, hpositiveColor, hpositiveNe⟩ := hpair
      let hpositive :
          ({color} : Finset (Fin 4)) ⊆
            system.positiveSignature positive := by
        simpa using hpositiveColor
      let hnegative :
          ({color} : Finset (Fin 4)) ⊆
            system.negativeSignature negative := by
        simpa [hnegativeExact]
      let reduced :=
        system.eraseEndpointColors positive negative {color}
          hpositive hnegative
      have hcard :
          (system.positiveSignature positive \ {color}).card = 1 :=
        signature_sdiff_singleton_card_eq_one hpositiveColor
          (system.positive_card_le_two positive) hpositiveNe
      obtain ⟨nextColor, hnext⟩ := Finset.card_eq_one.mp hcard
      have hnextReduced :
          reduced.positiveSignature positive = {nextColor} := by
        simpa [reduced] using hnext
      have hreduced : reduced.HasLinearForestMatching :=
        linearForestMatching_of_singleton reduced
          (Or.inl ⟨positive, nextColor, hnextReduced⟩)
      exact system.restore_negativeSingleton_forest positive negative color
        hpositiveColor hnegativeExact (by simpa [reduced] using hreduced)
    · obtain ⟨positive, hpositiveColor⟩ :=
        system.exists_positive_of_negative_mem hnegativeColor
      have hpositiveExact :
          system.positiveSignature positive = {color} := by
        by_contra hne
        exact hpair ⟨positive, hpositiveColor, hne⟩
      let hpositive :
          ({color} : Finset (Fin 4)) ⊆
            system.positiveSignature positive := by
        simpa [hpositiveExact]
      let hnegative :
          ({color} : Finset (Fin 4)) ⊆
            system.negativeSignature negative := by
        simpa [hnegativeExact]
      let reduced :=
        system.eraseEndpointColors positive negative {color}
          hpositive hnegative
      by_cases hnext :
          (∃ other nextColor,
              reduced.positiveSignature other = {nextColor}) ∨
            ∃ other nextColor,
              reduced.negativeSignature other = {nextColor}
      · have hreduced :=
          linearForestMatching_of_singleton reduced hnext
        exact system.restore_negativeSingleton_forest positive negative color
          hpositiveColor hnegativeExact (by simpa [reduced] using hreduced)
      · have hpositiveUnused :
            ∀ other, color ∉ reduced.positiveSignature other := by
          intro other hcolor
          by_cases hother : other = positive
          · subst other
            rw [ColorSignatureSystem.eraseEndpointColors_positive_at,
              hpositiveExact] at hcolor
            simp at hcolor
          · have horiginal :
                color ∈ system.positiveSignature other :=
              system.eraseEndpointColors_positive_subset
                positive negative {color} hpositive hnegative other hcolor
            have hexact :
                system.positiveSignature other = {color} := by
              by_contra hne
              exact hpair ⟨other, horiginal, hne⟩
            apply hnext
            left
            refine ⟨other, color, ?_⟩
            simp [reduced, ColorSignatureSystem.eraseEndpointColors,
              hother, hexact]
        have hnegativeUnused :
            ∀ other, color ∉ reduced.negativeSignature other := by
          have hpositiveFilter :
              Finset.univ.filter
                  (fun other =>
                    color ∈ reduced.positiveSignature other) = ∅ := by
            apply Finset.filter_eq_empty_iff.mpr
            intro other _
            exact hpositiveUnused other
          have hnegativeCard :
              (Finset.univ.filter
                (fun other =>
                  color ∈ reduced.negativeSignature other)).card = 0 := by
            rw [← reduced.balanced color, hpositiveFilter]
            simp
          intro other hcolor
          have hmem :
              other ∈ Finset.univ.filter
                (fun vertex =>
                  color ∈ reduced.negativeSignature vertex) := by
            simp [hcolor]
          have := Finset.card_pos.mpr ⟨other, hmem⟩
          omega
        have hreduced := reduced.linearForestMatching_of_unusedColor
          color hpositiveUnused hnegativeUnused
        exact system.restore_negativeSingleton_forest positive negative color
          hpositiveColor hnegativeExact (by simpa [reduced] using hreduced)
termination_by target.incidenceWeight
decreasing_by
  all_goals
    exact system.eraseEndpointColors_incidenceWeight_lt
      _ _ _ _ _ (by simp)

private theorem pair_signatureImbalance_eq_zero_of_weights_eq_zero
    (hweights : system.pairImbalanceWeights = 0)
    {left right : Fin 4} (hne : left ≠ right) :
    system.signatureImbalance {left, right} = 0 := by
  have h01 : system.signatureImbalance {0, 1} = 0 := by
    change system.pairImbalanceWeights.edge01 = 0
    rw [hweights]
    rfl
  have h02 : system.signatureImbalance {0, 2} = 0 := by
    change system.pairImbalanceWeights.edge02 = 0
    rw [hweights]
    rfl
  have h03 : system.signatureImbalance {0, 3} = 0 := by
    change system.pairImbalanceWeights.edge03 = 0
    rw [hweights]
    rfl
  have h12 : system.signatureImbalance {1, 2} = 0 := by
    change system.pairImbalanceWeights.edge12 = 0
    rw [hweights]
    rfl
  have h13 : system.signatureImbalance {1, 3} = 0 := by
    change system.pairImbalanceWeights.edge13 = 0
    rw [hweights]
    rfl
  have h23 : system.signatureImbalance {2, 3} = 0 := by
    change system.pairImbalanceWeights.edge23 = 0
    rw [hweights]
    rfl
  fin_cases left <;> fin_cases right <;> simp_all
  all_goals
    rw [Finset.pair_comm]
    assumption

private theorem positiveSignatureCount_eq_zero_of_two_lt_card
    (signature : Finset (Fin 4))
    (hcard : 2 < signature.card) :
    system.positiveSignatureCount signature = 0 := by
  unfold positiveSignatureCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro positive _ hsignature
  have hle := system.positive_card_le_two positive
  rw [hsignature] at hle
  omega

private theorem negativeSignatureCount_eq_zero_of_two_lt_card
    (signature : Finset (Fin 4))
    (hcard : 2 < signature.card) :
    system.negativeSignatureCount signature = 0 := by
  unfold negativeSignatureCount
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro negative _ hsignature
  have hle := system.negative_card_le_two negative
  rw [hsignature] at hle
  omega

private theorem signatureImbalance_eq_zero_of_weights_eq_zero
    (hsingleton : system.singletonImbalancesVanish)
    (hweights : system.pairImbalanceWeights = 0)
    (signature : Finset (Fin 4))
    (hnonempty : signature.Nonempty) :
    system.signatureImbalance signature = 0 := by
  by_cases hcard : signature.card ≤ 2
  · have hpositive : 0 < signature.card :=
      Finset.card_pos.mpr hnonempty
    have hcases :
        signature.card = 1 ∨ signature.card = 2 := by
      omega
    rcases hcases with hone | htwo
    · obtain ⟨color, rfl⟩ := Finset.card_eq_one.mp hone
      exact hsingleton color
    · obtain ⟨left, right, hne, rfl⟩ :=
        Finset.card_eq_two.mp htwo
      exact system.pair_signatureImbalance_eq_zero_of_weights_eq_zero
        hweights hne
  · have htwoLt : 2 < signature.card := by omega
    rw [signatureImbalance,
      system.positiveSignatureCount_eq_zero_of_two_lt_card
        signature htwoLt,
      system.negativeSignatureCount_eq_zero_of_two_lt_card
        signature htwoLt]
    simp

/-- For four colors, the only obstruction to the equal-signature linear-forest
matching is a nonzero element of the unsigned incidence kernel of `K₄`. -/
theorem forest_or_nonzeroK4Trade
    (hsingleton : system.singletonImbalancesVanish) :
    system.HasLinearForestMatching ∨
      ∃ x y : ℤ,
        (x ≠ 0 ∨ y ≠ 0) ∧
          system.pairImbalanceWeights = K4EdgeWeights.trade x y := by
  have hbalance := system.hasFourColorBalanceEquations
  by_cases hweights : system.pairImbalanceWeights = 0
  · left
    apply system.linearForestMatching_of_nonemptySignature_balanced
    exact system.signatureImbalance_eq_zero_of_weights_eq_zero
      hsingleton hweights
  · right
    obtain ⟨x, y, htrade⟩ :=
      system.k4Trade_of_singleton_zero hsingleton hbalance
    refine ⟨x, y, ?_, htrade⟩
    by_contra hzero
    push Not at hzero
    rcases hzero with ⟨rfl, rfl⟩
    apply hweights
    simpa using htrade

end ColorSignatureSystem

end

end XORGame
end QIT

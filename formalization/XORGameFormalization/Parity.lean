/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# XOR-game parity spaces and support-gap transfer

This module isolates two structural facts that do not depend on a particular
quantum-strategy representation.

First, clause parities form vector spaces over `ZMod 2`.  Inclusion of such
spaces reverses inclusion of their dual annihilators, and a known inclusion
`R ≤ L` is an equality exactly when the reverse annihilator containment also
holds.  This is the linear-algebra step used to compare true-refutation parity
with integer-relation parity in the finite XOR incidence model
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:835-900].

Second, a positive lower bound on finite clause weights transfers any uniform
clause-wise loss to the corresponding weighted loss.  The normalized theorem
has the factor `card ClauseId * minWeight`.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uC

noncomputable section

/-- A parity space on a clause index type is a binary linear subspace. -/
abbrev ParitySpace (ClauseId : Type uC) :=
  Submodule (ZMod 2) (ClauseId → ZMod 2)

/--
Inclusion of binary parity spaces reverses inclusion of their dual
annihilators.
-/
theorem dualAnnihilator_anti_of_paritySpace_le
    {ClauseId : Type uC} {R L : ParitySpace ClauseId} (hRL : R ≤ L) :
    L.dualAnnihilator ≤ R.dualAnnihilator :=
  Submodule.dualAnnihilator_anti hRL

/--
If `R ≤ L`, equality of the parity spaces is equivalent to the extra,
reverse containment between their dual annihilators.
-/
theorem paritySpace_eq_iff_dualAnnihilator_le_of_le
    {ClauseId : Type uC} {R L : ParitySpace ClauseId} (hRL : R ≤ L) :
    R = L ↔ R.dualAnnihilator ≤ L.dualAnnihilator := by
  constructor
  · rintro rfl
    exact le_rfl
  · intro hAnn
    have hLR : L ≤ R :=
      (Subspace.dualAnnihilator_le_dualAnnihilator_iff
        (K := ZMod 2) (V := ClauseId → ZMod 2) (W := R) (W' := L)).mp hAnn
    exact le_antisymm hRL hLR

/--
Elementwise form of `paritySpace_eq_iff_dualAnnihilator_le_of_le`: once
`R ≤ L` is known, equality holds exactly when every functional annihilating
`R` also annihilates `L`.
-/
theorem paritySpace_eq_iff_forall_dual_annihilator_of_le
    {ClauseId : Type uC} {R L : ParitySpace ClauseId} (hRL : R ≤ L) :
    R = L ↔
      ∀ φ : Module.Dual (ZMod 2) (ClauseId → ZMod 2),
        φ ∈ R.dualAnnihilator → φ ∈ L.dualAnnihilator := by
  rw [paritySpace_eq_iff_dualAnnihilator_le_of_le hRL]
  rfl

/-- The value of fixed clause-wise winning probabilities under a weight function. -/
def weightedValue {ClauseId : Type uC} [Fintype ClauseId]
    (weight win : ClauseId → ℝ) : ℝ :=
  ∑ i, weight i * win i

/--
The value of fixed clause-wise winning probabilities under the uniform
distribution.  For an empty support this definition is zero; gap-transfer
theorems assume the support is nonempty.
-/
def uniformValue {ClauseId : Type uC} [Fintype ClauseId]
    (win : ClauseId → ℝ) : ℝ :=
  (∑ i, win i) / Fintype.card ClauseId

/--
A pointwise lower bound on the weights turns the sum of clause losses into
a lower bound on weighted loss.
-/
theorem minWeight_mul_sum_loss_le_weightedLoss
    {ClauseId : Type uC} [Fintype ClauseId]
    (weight loss : ClauseId → ℝ) (minWeight : ℝ)
    (hloss : ∀ i, 0 ≤ loss i)
    (hmin : ∀ i, minWeight ≤ weight i) :
    minWeight * (∑ i, loss i) ≤ ∑ i, weight i * loss i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hmin i) (hloss i)

/--
If the weights sum to one, weighted value has loss at least the minimum
weight times the total clause loss.
-/
theorem minWeight_mul_sum_one_sub_le_one_sub_weightedValue
    {ClauseId : Type uC} [Fintype ClauseId]
    (weight win : ClauseId → ℝ) (minWeight : ℝ)
    (hweight : ∑ i, weight i = 1)
    (hwin : ∀ i, win i ≤ 1)
    (hmin : ∀ i, minWeight ≤ weight i) :
    minWeight * (∑ i, (1 - win i)) ≤
      1 - weightedValue weight win := by
  calc
    minWeight * (∑ i, (1 - win i))
        ≤ ∑ i, weight i * (1 - win i) :=
      minWeight_mul_sum_loss_le_weightedLoss
        weight (fun i => 1 - win i) minWeight
        (fun i => sub_nonneg.mpr (hwin i)) hmin
    _ = 1 - weightedValue weight win := by
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib,
        weightedValue, hweight]

/-- Total clause loss is support size times the uniform-value gap. -/
theorem card_mul_one_sub_uniformValue
    {ClauseId : Type uC} [Fintype ClauseId] [Nonempty ClauseId]
    (win : ClauseId → ℝ) :
    (Fintype.card ClauseId : ℝ) * (1 - uniformValue win) =
      ∑ i, (1 - win i) := by
  have hcard : (Fintype.card ClauseId : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [uniformValue, div_eq_mul_inv]
  field_simp
  simp

/--
Normalized gap transfer: for a nonempty finite support, a pointwise minimum
weight turns a uniform-value gap into a weighted-value gap.
-/
theorem card_mul_minWeight_mul_uniformGap_le_weightedGap
    {ClauseId : Type uC} [Fintype ClauseId] [Nonempty ClauseId]
    (weight win : ClauseId → ℝ) (minWeight : ℝ)
    (hweight : ∑ i, weight i = 1)
    (hwin : ∀ i, win i ≤ 1)
    (hmin : ∀ i, minWeight ≤ weight i) :
    (Fintype.card ClauseId : ℝ) * minWeight * (1 - uniformValue win) ≤
      1 - weightedValue weight win := by
  calc
    (Fintype.card ClauseId : ℝ) * minWeight * (1 - uniformValue win) =
        minWeight *
          ((Fintype.card ClauseId : ℝ) * (1 - uniformValue win)) := by
            ring
    _ = minWeight * (∑ i, (1 - win i)) := by
      rw [card_mul_one_sub_uniformValue]
    _ ≤ 1 - weightedValue weight win :=
      minWeight_mul_sum_one_sub_le_one_sub_weightedValue
        weight win minWeight hweight hwin hmin

/--
A strict uniform gap remains strict under normalized weights bounded below
by a positive number.
-/
theorem weightedValue_lt_one_of_uniformValue_lt_one
    {ClauseId : Type uC} [Fintype ClauseId] [Nonempty ClauseId]
    (weight win : ClauseId → ℝ) (minWeight : ℝ)
    (hweight : ∑ i, weight i = 1)
    (hwin : ∀ i, win i ≤ 1)
    (hmin : ∀ i, minWeight ≤ weight i)
    (hmin_pos : 0 < minWeight)
    (huniform : uniformValue win < 1) :
    weightedValue weight win < 1 := by
  have hcard : 0 < (Fintype.card ClauseId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgap :
      (Fintype.card ClauseId : ℝ) * minWeight *
          (1 - uniformValue win) ≤
        1 - weightedValue weight win :=
    card_mul_minWeight_mul_uniformGap_le_weightedGap
      weight win minWeight hweight hwin hmin
  have hpositive :
      0 < (Fintype.card ClauseId : ℝ) * minWeight *
          (1 - uniformValue win) :=
    mul_pos (mul_pos hcard hmin_pos) (sub_pos.mpr huniform)
  linarith

end

end XORGame
end QIT

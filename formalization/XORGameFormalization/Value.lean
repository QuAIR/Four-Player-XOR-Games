/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Parity
public import Mathlib.Data.Real.Archimedean

/-!
# Strategy-level XOR-game value bounds

The elementary gap estimate in `XORGameFormalization.Parity` concerns one
fixed vector of clause-wise winning probabilities.  This module packages the
same estimate at the strategy-value level, defined as a supremum over an
arbitrary strategy class.

No attainment assumption is made: the argument bounds every strategy first
and then takes the supremum.  Consequently it applies equally to finite and
non-compact strategy models.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uC uS

noncomputable section

/--
The value of a strategy class for a fixed clause distribution.

The function `win s i` is the winning probability of strategy `s` on clause
`i`.  Analytic strategy models can instantiate `Strategy` and `win` without
changing the finite support argument below.
-/
def strategyValue {ClauseId : Type uC} [Fintype ClauseId]
    (Strategy : Type uS) (weight : ClauseId → ℝ)
    (win : Strategy → ClauseId → ℝ) : ℝ :=
  sSup (Set.range fun strategy => weightedValue weight (win strategy))

/--
A common uniform upper bound for every strategy gives the corresponding
weighted upper bound for the supremal strategy value.

The factor `card ClauseId * minWeight` is the sharp normalization supplied by
the finite support loss calculation.
-/
theorem strategyValue_le_of_uniformValue_le
    {ClauseId : Type uC} [Fintype ClauseId] [Nonempty ClauseId]
    {Strategy : Type uS} [Nonempty Strategy]
    (weight : ClauseId → ℝ) (win : Strategy → ClauseId → ℝ)
    (minWeight uniformBound : ℝ)
    (hweight : ∑ i, weight i = 1)
    (hwin : ∀ strategy i, win strategy i ≤ 1)
    (hmin : ∀ i, minWeight ≤ weight i)
    (hmin_nonneg : 0 ≤ minWeight)
    (huniform : ∀ strategy, uniformValue (win strategy) ≤ uniformBound) :
    strategyValue Strategy weight win ≤
      1 - (Fintype.card ClauseId : ℝ) * minWeight *
        (1 - uniformBound) := by
  unfold strategyValue
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨strategy, rfl⟩
  have hgap :=
    card_mul_minWeight_mul_uniformGap_le_weightedGap
      weight (win strategy) minWeight hweight (hwin strategy) hmin
  have hcard_nonneg : 0 ≤ (Fintype.card ClauseId : ℝ) := by positivity
  have hscale_nonneg :
      0 ≤ (Fintype.card ClauseId : ℝ) * minWeight :=
    mul_nonneg hcard_nonneg hmin_nonneg
  have huniform_gap :
      1 - uniformBound ≤ 1 - uniformValue (win strategy) := by
    linarith [huniform strategy]
  have hscaled_gap :
      (Fintype.card ClauseId : ℝ) * minWeight * (1 - uniformBound) ≤
        (Fintype.card ClauseId : ℝ) * minWeight *
          (1 - uniformValue (win strategy)) :=
    mul_le_mul_of_nonneg_left huniform_gap hscale_nonneg
  linarith

/--
If every strategy has uniform value at most a number strictly below one,
then every positive-support distribution has strategy value strictly below
one as well.
-/
theorem strategyValue_lt_one_of_uniformValue_lt_one
    {ClauseId : Type uC} [Fintype ClauseId] [Nonempty ClauseId]
    {Strategy : Type uS} [Nonempty Strategy]
    (weight : ClauseId → ℝ) (win : Strategy → ClauseId → ℝ)
    (minWeight uniformBound : ℝ)
    (hweight : ∑ i, weight i = 1)
    (hwin : ∀ strategy i, win strategy i ≤ 1)
    (hmin : ∀ i, minWeight ≤ weight i)
    (hmin_pos : 0 < minWeight)
    (huniform : ∀ strategy, uniformValue (win strategy) ≤ uniformBound)
    (huniform_lt_one : uniformBound < 1) :
    strategyValue Strategy weight win < 1 := by
  have hle :=
    strategyValue_le_of_uniformValue_le
      weight win minWeight uniformBound hweight hwin hmin
      hmin_pos.le huniform
  have hcard_pos : 0 < (Fintype.card ClauseId : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hgap_pos :
      0 < (Fintype.card ClauseId : ℝ) * minWeight *
        (1 - uniformBound) :=
    mul_pos (mul_pos hcard_pos hmin_pos) (sub_pos.mpr huniform_lt_one)
  linarith

end

end XORGame
end QIT

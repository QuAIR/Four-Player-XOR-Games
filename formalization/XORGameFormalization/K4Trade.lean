/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# The unsigned K4 incidence kernel

The four-color selected-block obstruction is controlled by the unsigned
vertex-edge incidence matrix of `K4`.  This module solves that integer
kernel symbolically: its six edge weights form a two-parameter trade.
-/

@[expose] public section

namespace QIT.XORGame

/-- Integer weights on the six unordered edges of the four-color graph. -/
structure K4EdgeWeights where
  /-- Weight on edge `01`. -/
  edge01 : ℤ
  /-- Weight on edge `02`. -/
  edge02 : ℤ
  /-- Weight on edge `03`. -/
  edge03 : ℤ
  /-- Weight on edge `12`. -/
  edge12 : ℤ
  /-- Weight on edge `13`. -/
  edge13 : ℤ
  /-- Weight on edge `23`. -/
  edge23 : ℤ
  deriving DecidableEq

instance : Zero K4EdgeWeights where
  zero := ⟨0, 0, 0, 0, 0, 0⟩

namespace K4EdgeWeights

/--
The unsigned incidence-kernel equations: the three edge weights incident to
each of the four colors sum to zero.
-/
def IsUnsignedKernel (weights : K4EdgeWeights) : Prop :=
  weights.edge01 + weights.edge02 + weights.edge03 = 0 ∧
    weights.edge01 + weights.edge12 + weights.edge13 = 0 ∧
    weights.edge02 + weights.edge12 + weights.edge23 = 0 ∧
    weights.edge03 + weights.edge13 + weights.edge23 = 0

/--
The two-parameter `K4` trade.  Opposite edges agree, and the three
opposite-edge classes have weights `x`, `y`, and `-x-y`.
-/
def trade (x y : ℤ) : K4EdgeWeights where
  edge01 := x
  edge02 := y
  edge03 := -x - y
  edge12 := -x - y
  edge13 := y
  edge23 := x

/-- Every two-parameter trade satisfies the unsigned incidence equations. -/
theorem isUnsignedKernel_trade (x y : ℤ) :
    IsUnsignedKernel (trade x y) := by
  simp [IsUnsignedKernel, trade]
  ring

/-- Every integer vector in the unsigned `K4` incidence kernel is a trade. -/
theorem eq_trade_of_isUnsignedKernel
    (weights : K4EdgeWeights)
    (hkernel : IsUnsignedKernel weights) :
    ∃ x y : ℤ, weights = trade x y := by
  rcases weights with ⟨edge01, edge02, edge03,
    edge12, edge13, edge23⟩
  change
    edge01 + edge02 + edge03 = 0 ∧
      edge01 + edge12 + edge13 = 0 ∧
      edge02 + edge12 + edge23 = 0 ∧
      edge03 + edge13 + edge23 = 0 at hkernel
  rcases hkernel with ⟨hzero, hone, htwo, hthree⟩
  refine ⟨edge01, edge02, ?_⟩
  change
    K4EdgeWeights.mk edge01 edge02 edge03 edge12 edge13 edge23 =
      K4EdgeWeights.mk edge01 edge02 (-edge01 - edge02)
        (-edge01 - edge02) edge02 edge01
  rw [K4EdgeWeights.mk.injEq]
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

/-- Symbolic parameterization of the unsigned `K4` incidence kernel. -/
theorem isUnsignedKernel_iff_eq_trade
    (weights : K4EdgeWeights) :
    IsUnsignedKernel weights ↔
      ∃ x y : ℤ, weights = trade x y := by
  constructor
  · exact eq_trade_of_isUnsignedKernel weights
  · rintro ⟨x, y, rfl⟩
    exact isUnsignedKernel_trade x y

/-- The trade vanishes exactly when both parameters vanish. -/
@[simp]
theorem trade_eq_zero_iff (x y : ℤ) :
    trade x y = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro hzero
    have h01 := congrArg edge01 hzero
    have h02 := congrArg edge02 hzero
    simpa [trade] using And.intro h01 h02
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The three edge weights incident to a color. -/
def incidentWeights
    (weights : K4EdgeWeights) : Fin 4 → Fin 3 → ℤ :=
  ![
    ![weights.edge01, weights.edge02, weights.edge03],
    ![weights.edge01, weights.edge12, weights.edge13],
    ![weights.edge02, weights.edge12, weights.edge23],
    ![weights.edge03, weights.edge13, weights.edge23]
  ]

/--
A nonzero unsigned `K4` trade uses every color: at each color at least one
incident edge has nonzero weight.
-/
theorem nonzero_incident
    (weights : K4EdgeWeights)
    (hkernel : IsUnsignedKernel weights)
    (hnonzero : weights ≠ 0)
    (color : Fin 4) :
    ∃ slot : Fin 3, incidentWeights weights color slot ≠ 0 := by
  obtain ⟨x, y, rfl⟩ :=
    eq_trade_of_isUnsignedKernel weights hkernel
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra hnot
    push Not at hnot
    exact hnonzero ((trade_eq_zero_iff x y).2 hnot)
  rcases hxy with hx | hy
  · fin_cases color
    · exact ⟨0, by simpa [incidentWeights, trade]⟩
    · exact ⟨0, by simpa [incidentWeights, trade]⟩
    · exact ⟨2, by simpa [incidentWeights, trade]⟩
    · exact ⟨2, by simpa [incidentWeights, trade]⟩
  · fin_cases color
    · exact ⟨1, by simpa [incidentWeights, trade]⟩
    · exact ⟨2, by simpa [incidentWeights, trade]⟩
    · exact ⟨0, by simpa [incidentWeights, trade]⟩
    · exact ⟨1, by simpa [incidentWeights, trade]⟩

end K4EdgeWeights

end QIT.XORGame

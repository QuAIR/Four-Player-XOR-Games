/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.AllLength

/-!
# FourXOR: game-level pair-count expansion for the all-length obstruction

This file connects the combinatorial core (`altSum`, `pairSum`) to the
Cayley-game clause structure.  For a clause word of the Cayley game of a
finite additive group `G`, the degree-one alternating sums expand into the
clause sums `V_g`, `W_g`, and the class-two pair counts expand into the
ordered pair counts `R`, `P`, `Q`, `S`.  The product identities
`R_ij + R_ji = V_i V_j`, `P_ig + Q_gi = V_i W_g`, `S_gh + S_hg = W_g W_h`
and the degree-one structure lemma are proved here.
-/

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

attribute [local instance] Classical.propDecidable

/-- A clause of the Cayley game of `G`: `(g, false)` is `E_g` and
`(g, true)` is `O_g`. -/
abbrev GameClause (G : Type*) := G × Bool

/-- The letter received by player `α` from clause `c`. -/
def letterG (c : GameClause G) (α : G) : G := if c.2 then c.1 + α else c.1

/-- The target parity of a clause as an integer. -/
def parityG (c : GameClause G) : ℤ := if c.2 ∧ c.1 = 0 then 1 else 0

/-- Projection of a clause word onto player `α`. -/
def projectionG (w : List (GameClause G)) (α : G) : List G :=
  w.map (fun c => letterG c α)

/-- `E`-clause predicate. -/
def isE (c : GameClause G) : Prop := c.2 = false

/-- `O`-clause predicate. -/
def isO (c : GameClause G) : Prop := c.2 = true

/-- The clause has question `g`. -/
def hasG (g : G) (c : GameClause G) : Prop := c.1 = g

/-- Alternating sum over the `E_g` positions. -/
noncomputable def Vsum (w : List (GameClause G)) (g : G) : ℤ :=
  signedSum w (fun c => isE c ∧ hasG g c)

/-- Alternating sum over the `O_g` positions. -/
noncomputable def Wsum (w : List (GameClause G)) (g : G) : ℤ :=
  signedSum w (fun c => isO c ∧ hasG g c)

/-- Ordered pair count `E_i` before `E_j`. -/
noncomputable def Rsum (w : List (GameClause G)) (i j : G) : ℤ :=
  pairSumClause w (fun c => isE c ∧ hasG i c) (fun c => isE c ∧ hasG j c)

/-- Ordered pair count `E_i` before `O_g`. -/
noncomputable def Psum (w : List (GameClause G)) (i g : G) : ℤ :=
  pairSumClause w (fun c => isE c ∧ hasG i c) (fun c => isO c ∧ hasG g c)

/-- Ordered pair count `O_g` before `E_j`. -/
noncomputable def Qsum (w : List (GameClause G)) (g j : G) : ℤ :=
  pairSumClause w (fun c => isO c ∧ hasG g c) (fun c => isE c ∧ hasG j c)

/-- Ordered pair count `O_g` before `O_h`. -/
noncomputable def Ssum (w : List (GameClause G)) (g h : G) : ℤ :=
  pairSumClause w (fun c => isO c ∧ hasG g c) (fun c => isO c ∧ hasG h c)

/-- Disjoint predicates split `signedSum` additively. -/
lemma signedSum_or {α : Type*} (w : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred (fun a => P a ∨ Q a)]
    (hdisj : ∀ a, ¬ (P a ∧ Q a)) :
    signedSum w (fun a => P a ∨ Q a) = signedSum w P + signedSum w Q := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp only [signedSum]
      by_cases hpa : P a <;> by_cases hqa : Q a
      · exfalso
        exact hdisj a ⟨hpa, hqa⟩
      · simp [hpa, hqa, ih] <;> ring_nf
      · simp [hpa, hqa, ih] <;> ring_nf
      · simp [hpa, hqa, ih] <;> ring_nf

/-- Pointwise equivalent predicates give equal `signedSum`s. -/
lemma signedSum_congr {α : Type*} (w : List α) {P Q : α → Prop}
    [DecidablePred P] [DecidablePred Q] (h : ∀ a, P a ↔ Q a) :
    signedSum w P = signedSum w Q := by
  induction w with
  | nil => rfl
  | cons a l ih => simp [signedSum, h a, ih]

/-- Disjoint predicates split `pairSumClause` additively on the left. -/
lemma pairSumClause_or_left {α : Type*} (w : List α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    [DecidablePred (fun a => P a ∨ Q a)]
    (hdisj : ∀ a, ¬ (P a ∧ Q a)) :
    pairSumClause w (fun a => P a ∨ Q a) R =
      pairSumClause w P R + pairSumClause w Q R := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp only [pairSumClause]
      by_cases hpa : P a <;> by_cases hqa : Q a
      · exfalso
        exact hdisj a ⟨hpa, hqa⟩
      · simp [hpa, hqa, ih] <;> ring_nf
      · simp [hpa, hqa, ih] <;> ring_nf
      · simp [hpa, hqa, ih] <;> ring_nf

/-- Disjoint predicates split `pairSumClause` additively on the right. -/
lemma pairSumClause_or_right {α : Type*} (w : List α) (P Q R : α → Prop)
    [DecidablePred P] [DecidablePred Q] [DecidablePred R]
    [DecidablePred (fun a => Q a ∨ R a)]
    (hdisj : ∀ a, ¬ (Q a ∧ R a)) :
    pairSumClause w P (fun a => Q a ∨ R a) =
      pairSumClause w P Q + pairSumClause w P R := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp only [pairSumClause]
      rw [signedSum_or l Q R (fun b hb => hdisj b hb)]
      rw [ih]
      ring

/-- Pointwise equivalent predicates give equal `pairSumClause`s. -/
lemma pairSumClause_congr {α : Type*} (w : List α) {P P' Q Q' : α → Prop}
    [DecidablePred P] [DecidablePred P'] [DecidablePred Q] [DecidablePred Q']
    (hP : ∀ a, P a ↔ P' a) (hQ : ∀ a, Q a ↔ Q' a) :
    pairSumClause w P Q = pairSumClause w P' Q' := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp [pairSumClause, signedSum_congr l hQ, hP a, hQ a, ih]

/-- The letter of an `O`-clause equals `j` iff its question is `j - α`. -/
lemma letter_eq_iff (c : GameClause G) (α j : G) :
    letterG c α = j ↔ (isE c ∧ hasG j c) ∨ (isO c ∧ hasG (j - α) c) := by
  by_cases h : c.2 = true
  · simp [letterG, isE, isO, hasG, h]
    rw [eq_sub_iff_add_eq]
  · have hf : c.2 = false := Bool.eq_false_of_not_eq_true h
    simp [letterG, isE, isO, hasG, hf]

/-- Degree-one expansion: the alternating letter sum of the projection is
`V_j + W_{j-α}`. -/
lemma altSum_projection (w : List (GameClause G)) (α j : G) :
    altSum (projectionG w α) j = Vsum w j + Wsum w (j - α) := by
  classical
  rw [projectionG, altSum_map]
  rw [signedSum_congr w (fun c => letter_eq_iff c α j)]
  rw [signedSum_or w (fun c => isE c ∧ hasG j c) (fun c => isO c ∧ hasG (j - α) c)]
  · rfl
  · intro c h
    exact Bool.false_ne_true (h.1.1.symm.trans h.2.1)

/-- Class-two expansion: the ordered pair count of the projection is
`R_ij + P_{i,j-α} + Q_{i-α,j} + S_{i-α,j-α}`. -/
lemma pairSum_projection (w : List (GameClause G)) (α i j : G) (hij : i ≠ j) :
    pairSum (projectionG w α) i j =
      Rsum w i j + Psum w i (j - α) + Qsum w (i - α) j + Ssum w (i - α) (j - α) := by
  classical
  rw [projectionG, pairSum_map]
  rw [pairSumClause_congr w (fun c => letter_eq_iff c α i) (fun c => letter_eq_iff c α j)]
  rw [pairSumClause_or_left w (fun c => isE c ∧ hasG i c) (fun c => isO c ∧ hasG (i - α) c)
      (fun c => (isE c ∧ hasG j c) ∨ (isO c ∧ hasG (j - α) c))]
  · rw [pairSumClause_or_right w (fun c => isE c ∧ hasG i c)
        (fun c => isE c ∧ hasG j c) (fun c => isO c ∧ hasG (j - α) c)]
    · rw [pairSumClause_or_right w (fun c => isO c ∧ hasG (i - α) c)
          (fun c => isE c ∧ hasG j c) (fun c => isO c ∧ hasG (j - α) c)]
      · simp [Rsum, Psum, Qsum, Ssum] <;> ring_nf
      · intro c h
        exact Bool.false_ne_true (h.1.1.symm.trans h.2.1)
    · intro c h
      exact Bool.false_ne_true (h.1.1.symm.trans h.2.1)
  · intro c h
    exact Bool.false_ne_true (h.1.1.symm.trans h.2.1)

/-- Symmetric pair counts give the product of the signed sums. -/
lemma pairSumClause_symm {α : Type*} (w : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q]
    (hdisj : ∀ a, ¬ (P a ∧ Q a)) :
    pairSumClause w P Q + pairSumClause w Q P = signedSum w P * signedSum w Q := by
  induction w with
  | nil => simp [pairSumClause, signedSum]
  | cons a l ih =>
      simp only [pairSumClause, signedSum]
      have hpq : (if P a then 1 else 0) * (if Q a then 1 else 0) = 0 := by
        by_cases hpa : P a <;> by_cases hqa : Q a
        · exfalso
          exact hdisj a ⟨hpa, hqa⟩
        · simp [hpa, hqa]
        · simp [hpa, hqa]
        · simp [hpa, hqa]
      nlinarith [ih, hpq]

/-- `VV`: `R_ij + R_ji = V_i V_j` for `i ≠ j`. -/
lemma VV (w : List (GameClause G)) (i j : G) (hij : i ≠ j) :
    Rsum w i j + Rsum w j i = Vsum w i * Vsum w j := by
  classical
  exact pairSumClause_symm w (fun c => isE c ∧ hasG i c) (fun c => isE c ∧ hasG j c) (by
    intro c h
    exact hij (h.1.2.symm.trans h.2.2))

/-- `PW`: `P_ig + Q_gi = V_i W_g`. -/
lemma PW (w : List (GameClause G)) (i g : G) :
    Psum w i g + Qsum w g i = Vsum w i * Wsum w g := by
  classical
  exact pairSumClause_symm w (fun c => isE c ∧ hasG i c) (fun c => isO c ∧ hasG g c) (by
    intro c h
    exact Bool.false_ne_true (h.1.1.symm.trans h.2.1))

/-- `WW`: `S_gh + S_hg = W_g W_h` for `g ≠ h`. -/
lemma WW (w : List (GameClause G)) (g h : G) (hgh : g ≠ h) :
    Ssum w g h + Ssum w h g = Wsum w g * Wsum w h := by
  classical
  exact pairSumClause_symm w (fun c => isO c ∧ hasG g c) (fun c => isO c ∧ hasG h c) (by
    intro c h
    exact hgh (h.1.2.symm.trans h.2.2))

/-- The degree-one conditions force a common value `v` with `W_g = -v`
and `V_j = v`. -/
lemma degree1_structure (w : List (GameClause G))
    (h : ∀ α j, Vsum w j + Wsum w (j + α) = 0) :
    ∃ v : ℤ, (∀ g, Wsum w g = -v) ∧ (∀ j, Vsum w j = v) := by
  refine ⟨Vsum w 0, ?_, ?_⟩
  · intro g
    have h0 := h g 0
    have h0' : Vsum w 0 + Wsum w g = 0 := by simpa using h0
    linarith
  · intro j
    have h0 := h 0 j
    have h0' : Vsum w j + Wsum w j = 0 := by simpa using h0
    have hw := h j 0
    have hw' : Vsum w 0 + Wsum w j = 0 := by simpa using hw
    linarith

end FourXOR
end Research
end QIT

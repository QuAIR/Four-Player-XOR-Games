/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.AllLengthGame

/-!
# FourXOR: the Klein V4 all-length obstruction

This file assembles the E' system and the parity lemma for the all-length
obstruction, then formalizes the explicit integer certificate that forces
`w = v^2` to be even on the Klein group `V4 = ZMod 2 × ZMod 2`.  Combined
with the oddness of `v`, this proves that the Klein game has no true
refutation of any length.
-/

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

attribute [local instance] Classical.propDecidable

/-- Count of positions satisfying a decidable predicate. -/
def countP {α : Type*} (w : List α) (P : α → Prop) [DecidablePred P] : ℕ :=
  (w.filter fun a => decide (P a)).length

/-- `(-x) % 2 = x % 2` for integers. -/
lemma Int.neg_emod_two (x : ℤ) : (-x) % 2 = x % 2 := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := Int.emod_two_eq_zero_or_one x
  rcases hx with hx | hx
  · have hdiv : (2 : ℤ) ∣ x := Int.dvd_of_emod_eq_zero hx
    rcases hdiv with ⟨k, hk⟩
    rw [hx]
    have hneg : (2 : ℤ) ∣ -x := by
      refine ⟨-k, ?_⟩
      rw [hk]
      ring
    exact Int.emod_eq_zero_of_dvd hneg
  · have hodd : Odd x := Int.odd_iff.mpr hx
    have hodd' : Odd (-x) := hodd.neg
    rw [hx, Int.odd_iff.mp hodd']

/-- `(1 - x) % 2 = (1 + x) % 2` for integers. -/
lemma emod_two_sub_add (x : ℤ) : (1 - x) % 2 = (1 + x) % 2 := by
  have hx : x % 2 = 0 ∨ x % 2 = 1 := Int.emod_two_eq_zero_or_one x
  rcases hx with hx | hx
  · rw [Int.sub_emod, Int.add_emod, hx]
    norm_num
  · rw [Int.sub_emod, Int.add_emod, hx]
    norm_num

/-- `1 + x` respects integer parity. -/
lemma emod_two_add (x y : ℤ) (h : x % 2 = y % 2) : (1 + x) % 2 = (1 + y) % 2 := by
  conv_rhs => rw [Int.add_emod]
  rw [Int.add_emod, h]

/-- `1 - x` respects integer parity. -/
lemma emod_two_sub (x y : ℤ) (h : x % 2 = y % 2) : (1 - x) % 2 = (1 - y) % 2 := by
  conv_rhs => rw [Int.sub_emod]
  rw [Int.sub_emod, h]

/-- An odd integer is not even. -/
lemma odd_not_even {a : ℤ} (ho : Odd a) (he : Even a) : False := by
  rcases ho with ⟨k, hk⟩
  rcases he with ⟨m, hm⟩
  have h : (2 : ℤ) * k + 1 = 2 * m := by
    rw [← hk, hm]
    ring
  omega

/-- A signed sum has the parity of its count. -/
lemma signedSum_mod_two {α : Type*} (w : List α) (P : α → Prop) [DecidablePred P] :
    signedSum w P % 2 = (((countP w P : ℕ) : ℤ)) % 2 := by
  induction w with
  | nil => simp [signedSum, countP]
  | cons a l ih =>
      by_cases h : P a
      · have hdec : decide (P a) = true := by simp [h]
        simp [signedSum, countP, h, hdec]
        rw [emod_two_sub_add, emod_two_add _ _ ih]
        simp [countP]
        rw [add_comm]
      · have hdec : decide (P a) = false := by simp [h]
        simp [signedSum, countP, h, hdec]
        exact ih

/-- Number of `O_0` clauses in a word. -/
def O0Count (w : List (GameClause G)) : ℕ :=
  countP w (fun c => c.2 = true ∧ c.1 = 0)

/-- A true refutation of the Cayley game of `G`: every projection reduces and
the `O_0` count is odd. -/
def IsTrueRefutationG (w : List (GameClause G)) : Prop :=
  (∀ α : G, Reducible (projectionG w α)) ∧ Odd (O0Count w)

/-- `W_0` has the parity of the `O_0` count. -/
lemma W0_mod_two (w : List (GameClause G)) :
    Wsum w 0 % 2 = (((O0Count w : ℕ) : ℤ)) % 2 := by
  induction w with
  | nil => simp [Wsum, O0Count, countP, signedSum]
  | cons c l ih =>
      by_cases h : isO c ∧ hasG 0 c
      · have hdec : decide (isO c ∧ hasG 0 c) = true := by simp [h]
        have hw : Wsum (c :: l) 0 = 1 - Wsum l 0 := by
          change (if isO c ∧ hasG 0 c then 1 else 0) - Wsum l 0 = 1 - Wsum l 0
          simp [h]
        have ho : O0Count (c :: l) = O0Count l + 1 := by
          simp [O0Count, countP]
          have hdec' : (c.2 && decide (c.1 = 0)) = true := by
            have h' : c.2 = true ∧ c.1 = 0 := by simpa [isO, hasG] using h
            have hd : decide (c.1 = 0) = true := decide_eq_true h'.2
            simp [h'.1, hd]
          have hfc : List.filter (fun a : GameClause G => a.2 && decide (a.1 = 0)) (c :: l) =
              c :: List.filter (fun a : GameClause G => a.2 && decide (a.1 = 0)) l :=
            List.filter_cons_of_pos (p := fun a : GameClause G => a.2 && decide (a.1 = 0)) hdec'
          rw [hfc]
          simp
        rw [hw, ho]
        rw [emod_two_sub_add, emod_two_add _ _ ih]
        simp [Nat.cast_add]
        rw [add_comm]
      · have hdec : decide (isO c ∧ hasG 0 c) = false := by simp [h]
        have hw : Wsum (c :: l) 0 = - Wsum l 0 := by
          change (if isO c ∧ hasG 0 c then 1 else 0) - Wsum l 0 = - Wsum l 0
          simp [h]
        have ho : O0Count (c :: l) = O0Count l := by
          simp [O0Count, countP]
          have hdec' : (c.2 && decide (c.1 = 0)) = false := by
            have h' : ¬ (c.2 = true ∧ c.1 = 0) := by simpa [isO, hasG] using h
            by_cases hc2 : c.2 = true
            · by_cases hc1 : c.1 = 0
              · exfalso
                exact h' ⟨hc2, hc1⟩
              · have hd : decide (c.1 = 0) = false := decide_eq_false hc1
                simp [hc2, hd]
            · have hf : c.2 = false := Bool.eq_false_of_not_eq_true hc2
              rw [hf]
              rfl
          have hneg : ¬ (c.2 && decide (c.1 = 0)) = true := by
            intro htr
            have hc : true = false := by
              rw [← htr, hdec']
            exact Bool.false_ne_true hc.symm
          have hfc : List.filter (fun a : GameClause G => a.2 && decide (a.1 = 0)) (c :: l) =
              List.filter (fun a : GameClause G => a.2 && decide (a.1 = 0)) l :=
            List.filter_cons_of_neg (p := fun a : GameClause G => a.2 && decide (a.1 = 0)) hneg
          rw [hfc]
        rw [hw, ho, Int.neg_emod_two, ih]

/-- The parity of `W_0` equals the parity of the `O_0` count. -/
lemma W0_odd_iff (w : List (GameClause G)) :
    Odd (Wsum w 0) ↔ Odd (O0Count w) := by
  constructor
  · intro h
    have hz : ((O0Count w : ℕ) : ℤ) % 2 = 1 := by
      have hodd : Wsum w 0 % 2 = 1 := Int.odd_iff.mp h
      rw [W0_mod_two w] at hodd
      exact hodd
    have hoddZ : Odd ((O0Count w : ℕ) : ℤ) := Int.odd_iff.mpr hz
    rw [Nat.odd_iff]
    have hcast : ((O0Count w % 2 : ℕ) : ℤ) = 1 := by
      have hmod := Int.natCast_emod (O0Count w) 2
      rw [hmod]
      exact hz
    exact_mod_cast hcast
  · intro h
    have hn : (O0Count w) % 2 = 1 := Nat.odd_iff.mp h
    have hcast : ((O0Count w % 2 : ℕ) : ℤ) = 1 := by exact_mod_cast hn
    have hz : ((O0Count w : ℕ) : ℤ) % 2 = 1 := by
      have hmod := Int.natCast_emod (O0Count w) 2
      simpa [hmod] using hcast
    have hodd : Wsum w 0 % 2 = 1 := by
      rw [W0_mod_two w]
      exact hz
    exact Int.odd_iff.mpr hodd

/-- The E' equation from the class-two conditions. -/
lemma Eprime (w : List (GameClause G))
    (hw : ∀ α : G, Reducible (projectionG w α))
    (i j c : G) (hij : i ≠ j) :
    Rsum w i j + Psum w i (j + c) + Qsum w (i + c) j + Ssum w (i + c) (j + c) = 0 := by
  have h0 := pairSum_reducible hij (hw (-c))
  have hx := pairSum_projection w (-c) i j hij
  rw [hx] at h0
  simpa [sub_neg_eq_add] using h0

end FourXOR
end Research
end QIT

/-! # The Klein V4 certificate -/

namespace QIT
namespace Research
namespace FourXOR

/-- The Klein group. -/
abbrev V4 := ZMod 2 × ZMod 2

abbrev v0 : V4 := (0, 0)
abbrev v1 : V4 := (1, 0)
abbrev v2 : V4 := (0, 1)
abbrev v3 : V4 := (1, 1)

set_option maxHeartbeats 800000 in
lemma v4_parity_certificate
    (R P Q S : V4 → V4 → ℤ) (w : ℤ)
    (hE : ∀ i j c, i ≠ j → i ≠ v0 → j ≠ v0 →
      R i j + P i (j + c) + Q (i + c) j + S (i + c) (j + c) = 0)
    (hVV : ∀ i j, i ≠ j → R i j + R j i = w)
    (hPW : ∀ i g, i ≠ v0 → P i g + Q g i = -w) :
    8 * (R v1 v2 + Q v1 v3 - Q v2 v3 - Q v3 v1 + Q v3 v2 - S v3 v1 + S v3 v2) = 4 * w := by
  have hz2 : (2 : ZMod 2) = 0 := by decide
  have hE12_0 : R v1 v2 + P v1 v2 + Q v1 v2 + S v1 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v2 v0 (by decide) (by decide) (by decide)
  have hE12_1 : R v1 v2 + P v1 v3 + Q v0 v2 + S v0 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v2 v1 (by decide) (by decide) (by decide)
  have hE12_2 : R v1 v2 + P v1 v0 + Q v3 v2 + S v3 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v2 v2 (by decide) (by decide) (by decide)
  have hE12_3 : R v1 v2 + P v1 v1 + Q v2 v2 + S v2 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v2 v3 (by decide) (by decide) (by decide)
  have hE13_0 : R v1 v3 + P v1 v3 + Q v1 v3 + S v1 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v3 v0 (by decide) (by decide) (by decide)
  have hE13_1 : R v1 v3 + P v1 v2 + Q v0 v3 + S v0 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v3 v1 (by decide) (by decide) (by decide)
  have hE13_2 : R v1 v3 + P v1 v1 + Q v3 v3 + S v3 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v3 v2 (by decide) (by decide) (by decide)
  have hE13_3 : R v1 v3 + P v1 v0 + Q v2 v3 + S v2 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v1 v3 v3 (by decide) (by decide) (by decide)
  have hE21_0 : R v2 v1 + P v2 v1 + Q v2 v1 + S v2 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v1 v0 (by decide) (by decide) (by decide)
  have hE21_1 : R v2 v1 + P v2 v0 + Q v3 v1 + S v3 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v1 v1 (by decide) (by decide) (by decide)
  have hE21_2 : R v2 v1 + P v2 v3 + Q v0 v1 + S v0 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v1 v2 (by decide) (by decide) (by decide)
  have hE21_3 : R v2 v1 + P v2 v2 + Q v1 v1 + S v1 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v1 v3 (by decide) (by decide) (by decide)
  have hE23_0 : R v2 v3 + P v2 v3 + Q v2 v3 + S v2 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v3 v0 (by decide) (by decide) (by decide)
  have hE23_1 : R v2 v3 + P v2 v2 + Q v3 v3 + S v3 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v3 v1 (by decide) (by decide) (by decide)
  have hE23_2 : R v2 v3 + P v2 v1 + Q v0 v3 + S v0 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v3 v2 (by decide) (by decide) (by decide)
  have hE23_3 : R v2 v3 + P v2 v0 + Q v1 v3 + S v1 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v2 v3 v3 (by decide) (by decide) (by decide)
  have hE31_0 : R v3 v1 + P v3 v1 + Q v3 v1 + S v3 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v1 v0 (by decide) (by decide) (by decide)
  have hE31_1 : R v3 v1 + P v3 v0 + Q v2 v1 + S v2 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v1 v1 (by decide) (by decide) (by decide)
  have hE31_2 : R v3 v1 + P v3 v3 + Q v1 v1 + S v1 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v1 v2 (by decide) (by decide) (by decide)
  have hE31_3 : R v3 v1 + P v3 v2 + Q v0 v1 + S v0 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v1 v3 (by decide) (by decide) (by decide)
  have hE32_0 : R v3 v2 + P v3 v2 + Q v3 v2 + S v3 v2 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v2 v0 (by decide) (by decide) (by decide)
  have hE32_1 : R v3 v2 + P v3 v3 + Q v2 v2 + S v2 v3 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v2 v1 (by decide) (by decide) (by decide)
  have hE32_2 : R v3 v2 + P v3 v0 + Q v1 v2 + S v1 v0 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v2 v2 (by decide) (by decide) (by decide)
  have hE32_3 : R v3 v2 + P v3 v1 + Q v0 v2 + S v0 v1 = 0 := by
    simpa [v0, v1, v2, v3, hz2] using hE v3 v2 v3 (by decide) (by decide) (by decide)
  have hVV12 : R v1 v2 + R v2 v1 = w := hVV v1 v2 (by decide)
  have hVV13 : R v1 v3 + R v3 v1 = w := hVV v1 v3 (by decide)
  have hVV23 : R v2 v3 + R v3 v2 = w := hVV v2 v3 (by decide)
  have hPW11 : P v1 v1 + Q v1 v1 = -w := hPW v1 v1 (by decide)
  have hPW12 : P v1 v2 + Q v2 v1 = -w := hPW v1 v2 (by decide)
  linear_combination (norm := simp [v0, v1, v2, v3] <;> ring_nf)
    (5 * hE12_0 - 3 * hE12_1 + 5 * hE12_2 - 3 * hE12_3)
    + (3 * hE13_0 + 3 * hE13_1 - 5 * hE13_2 - 5 * hE13_3)
    + (3 * hE21_0 - 5 * hE21_1 + 3 * hE21_2 - 5 * hE21_3)
    + (-3 * hE23_0 + 5 * hE23_1 - 3 * hE23_2 + 5 * hE23_3)
    + (-3 * hE31_0 + 5 * hE31_1 - 3 * hE31_2 - 3 * hE31_3)
    + (3 * hE32_0 + 3 * hE32_1 - 5 * hE32_2 + 3 * hE32_3)
    + 4 * hVV12 + 4 * hVV13 - 4 * hVV23
    + 8 * hPW11 - 8 * hPW12

/-- Corollary of the certificate: `w` is twice an integer, hence even. -/
lemma v4_parity_certificate_corollary
    (R P Q S : V4 → V4 → ℤ) (w : ℤ)
    (hE : ∀ i j c, i ≠ j → i ≠ v0 → j ≠ v0 →
      R i j + P i (j + c) + Q (i + c) j + S (i + c) (j + c) = 0)
    (hVV : ∀ i j, i ≠ j → R i j + R j i = w)
    (hPW : ∀ i g, i ≠ v0 → P i g + Q g i = -w) :
    w = 2 * (R v1 v2 + Q v1 v3 - Q v2 v3 - Q v3 v1 + Q v3 v2 - S v3 v1 + S v3 v2) := by
  have h := v4_parity_certificate R P Q S w hE hVV hPW
  linarith

/-- The Klein V4 Cayley game has no true refutation of any length. -/
theorem klein_no_refutation (w : List (GameClause V4))
    (hw : IsTrueRefutationG w) : False := by
  have h1 : ∀ α j : V4, Vsum w j + Wsum w (j + α) = 0 := by
    intro α j
    have hred' := altSum_reducible (hw.1 (-α)) j
    have hx'' := altSum_projection w (-α) j
    rw [hx''] at hred'
    simpa [sub_neg_eq_add] using hred'
  obtain ⟨v, hvW, hvV⟩ := degree1_structure w h1
  have hoddv : Odd v := by
    have hwo : Odd (Wsum w 0) := (W0_odd_iff w).mpr hw.2
    have hw0 : Wsum w 0 = -v := hvW 0
    have hneg : Odd (-v) := by simpa [hw0] using hwo
    simpa using (hneg.neg : Odd (-(-v)))
  have hE' : ∀ i j c : V4, i ≠ j → i ≠ v0 → j ≠ v0 →
      Rsum w i j + Psum w i (j + c) + Qsum w (i + c) j + Ssum w (i + c) (j + c) = 0 := by
    intro i j c hij hi0 hj0
    exact Eprime w hw.1 i j c hij
  have hVV' : ∀ i j : V4, i ≠ j → Rsum w i j + Rsum w j i = v * v := by
    intro i j hij
    rw [VV w i j hij, hvV i, hvV j]
  have hPW' : ∀ i g : V4, i ≠ v0 → Psum w i g + Qsum w g i = -(v * v) := by
    intro i g hi0
    rw [PW w i g, hvV i, hvW g]
    ring
  have hcert := v4_parity_certificate_corollary (Rsum w) (Psum w) (Qsum w) (Ssum w) (v * v)
    hE' hVV' hPW'
  have heven : Even (v * v) := by
    refine ⟨(Rsum w v1 v2 + Qsum w v1 v3 - Qsum w v2 v3 - Qsum w v3 v1 +
      Qsum w v3 v2 - Ssum w v3 v1 + Ssum w v3 v2), ?_⟩
    rw [hcert]
    ring
  have hodd : Odd (v * v) := Odd.mul hoddv hoddv
  exact odd_not_even hodd heven

end FourXOR
end Research
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.AllLengthV4
import FourXOR.CayleyPREF

/-!
# FourXOR: the all-length obstruction for `F_2^r`

The Klein `V4` certificate is transported to every elementary abelian
`2`-group `F_2^r` (`r ≥ 2`) through a generalized certificate valid in any
additive group of exponent two with a distinguished triple `z1, z2, z1+z2`.
This proves the elementary-abelian all-length obstruction: the Cayley game of
`F_2^r` has no true refutation of any length.
-/

namespace QIT
namespace Research
namespace FourXOR

/-- In `ZMod 2`, every element is its own additive inverse. -/
lemma zmod2_add_self (a : ZMod 2) : a + a = 0 := by
  fin_cases a <;> decide

/-- Pointwise, every function into `ZMod 2` has exponent two. -/
lemma pi_zmod2_add_self {ι : Type*} (x : ι → ZMod 2) : x + x = 0 := by
  funext i
  exact zmod2_add_self (x i)

set_option maxHeartbeats 800000 in
lemma certificate_general {G : Type*} [AddCommGroup G] [DecidableEq G]
    (z1 z2 z3 : G)
    (h12 : z1 ≠ z2) (h13 : z1 ≠ z3) (h23 : z2 ≠ z3)
    (h1n : z1 ≠ 0) (h2n : z2 ≠ 0) (h3n : z3 ≠ 0)
    (hsum : z1 + z2 = z3)
    (h2 : ∀ x : G, x + x = 0)
    (R P Q S : G → G → ℤ) (w : ℤ)
    (hE : ∀ i j c, i ≠ j → i ≠ 0 → j ≠ 0 →
      R i j + P i (j + c) + Q (i + c) j + S (i + c) (j + c) = 0)
    (hVV : ∀ i j, i ≠ j → R i j + R j i = w)
    (hPW : ∀ i g, i ≠ 0 → P i g + Q g i = -w) :
    8 * (R z1 z2 + Q z1 z3 - Q z2 z3 - Q z3 z1 + Q z3 z2 - S z3 z1 + S z3 z2) = 4 * w := by
  have hz2z1 : z2 + z1 = z3 := by
    rw [add_comm, hsum]
  have hz1z1 : z1 + z1 = 0 := h2 z1
  have hz2z2 : z2 + z2 = 0 := h2 z2
  have hz3z3 : z3 + z3 = 0 := h2 z3
  have hz1z3 : z1 + z3 = z2 := by
    rw [← hsum]
    rw [← add_assoc, hz1z1, zero_add]
  have hz3z1 : z3 + z1 = z2 := by
    rw [add_comm, hz1z3]
  have hz2z3 : z2 + z3 = z1 := by
    rw [← hsum]
    rw [add_left_comm, hz2z2, add_zero]
  have hz3z2 : z3 + z2 = z1 := by
    rw [add_comm, hz2z3]
  have hE12_0 : R z1 z2 + P z1 z2 + Q z1 z2 + S z1 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z1 z2 0 h12 h1n h2n
  have hE12_1 : R z1 z2 + P z1 z3 + Q 0 z2 + S 0 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z2 z1 h12 h1n h2n
  have hE12_2 : R z1 z2 + P z1 0 + Q z3 z2 + S z3 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z2 z2 h12 h1n h2n
  have hE12_3 : R z1 z2 + P z1 z1 + Q z2 z2 + S z2 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z2 z3 h12 h1n h2n
  have hE13_0 : R z1 z3 + P z1 z3 + Q z1 z3 + S z1 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z1 z3 0 h13 h1n h3n
  have hE13_1 : R z1 z3 + P z1 z2 + Q 0 z3 + S 0 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z3 z1 h13 h1n h3n
  have hE13_2 : R z1 z3 + P z1 z1 + Q z3 z3 + S z3 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z3 z2 h13 h1n h3n
  have hE13_3 : R z1 z3 + P z1 0 + Q z2 z3 + S z2 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z1 z3 z3 h13 h1n h3n
  have hE21_0 : R z2 z1 + P z2 z1 + Q z2 z1 + S z2 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z2 z1 0 h12.symm h2n h1n
  have hE21_1 : R z2 z1 + P z2 0 + Q z3 z1 + S z3 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z1 z1 h12.symm h2n h1n
  have hE21_2 : R z2 z1 + P z2 z3 + Q 0 z1 + S 0 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z1 z2 h12.symm h2n h1n
  have hE21_3 : R z2 z1 + P z2 z2 + Q z1 z1 + S z1 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z1 z3 h12.symm h2n h1n
  have hE23_0 : R z2 z3 + P z2 z3 + Q z2 z3 + S z2 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z2 z3 0 h23 h2n h3n
  have hE23_1 : R z2 z3 + P z2 z2 + Q z3 z3 + S z3 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z3 z1 h23 h2n h3n
  have hE23_2 : R z2 z3 + P z2 z1 + Q 0 z3 + S 0 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z3 z2 h23 h2n h3n
  have hE23_3 : R z2 z3 + P z2 0 + Q z1 z3 + S z1 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z2 z3 z3 h23 h2n h3n
  have hE31_0 : R z3 z1 + P z3 z1 + Q z3 z1 + S z3 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z3 z1 0 h13.symm h3n h1n
  have hE31_1 : R z3 z1 + P z3 0 + Q z2 z1 + S z2 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z1 z1 h13.symm h3n h1n
  have hE31_2 : R z3 z1 + P z3 z3 + Q z1 z1 + S z1 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z1 z2 h13.symm h3n h1n
  have hE31_3 : R z3 z1 + P z3 z2 + Q 0 z1 + S 0 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z1 z3 h13.symm h3n h1n
  have hE32_0 : R z3 z2 + P z3 z2 + Q z3 z2 + S z3 z2 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using hE z3 z2 0 h23.symm h3n h2n
  have hE32_1 : R z3 z2 + P z3 z3 + Q z2 z2 + S z2 z3 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z2 z1 h23.symm h3n h2n
  have hE32_2 : R z3 z2 + P z3 0 + Q z1 z2 + S z1 0 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z2 z2 h23.symm h3n h2n
  have hE32_3 : R z3 z2 + P z3 z1 + Q 0 z2 + S 0 z1 = 0 := by
    simpa [hsum, hz2z1, hz1z1, hz2z2, hz3z3, hz1z3, hz3z1, hz2z3, hz3z2] using
      hE z3 z2 z3 h23.symm h3n h2n
  have hVV12 : R z1 z2 + R z2 z1 = w := hVV z1 z2 h12
  have hVV13 : R z1 z3 + R z3 z1 = w := hVV z1 z3 h13
  have hVV23 : R z2 z3 + R z3 z2 = w := hVV z2 z3 h23
  have hPW11 : P z1 z1 + Q z1 z1 = -w := hPW z1 z1 h1n
  have hPW12 : P z1 z2 + Q z2 z1 = -w := hPW z1 z2 h1n
  linear_combination (norm := ring_nf)
    (5 * hE12_0 - 3 * hE12_1 + 5 * hE12_2 - 3 * hE12_3)
    + (3 * hE13_0 + 3 * hE13_1 - 5 * hE13_2 - 5 * hE13_3)
    + (3 * hE21_0 - 5 * hE21_1 + 3 * hE21_2 - 5 * hE21_3)
    + (-3 * hE23_0 + 5 * hE23_1 - 3 * hE23_2 + 5 * hE23_3)
    + (-3 * hE31_0 + 5 * hE31_1 - 3 * hE31_2 - 3 * hE31_3)
    + (3 * hE32_0 + 3 * hE32_1 - 5 * hE32_2 + 3 * hE32_3)
    + 4 * hVV12 + 4 * hVV13 - 4 * hVV23
    + 8 * hPW11 - 8 * hPW12

/-- Corollary of the generalized certificate: `w` is twice an integer. -/
lemma certificate_general_corollary {G : Type*} [AddCommGroup G] [DecidableEq G]
    (z1 z2 z3 : G)
    (h12 : z1 ≠ z2) (h13 : z1 ≠ z3) (h23 : z2 ≠ z3)
    (h1n : z1 ≠ 0) (h2n : z2 ≠ 0) (h3n : z3 ≠ 0)
    (hsum : z1 + z2 = z3)
    (h2 : ∀ x : G, x + x = 0)
    (R P Q S : G → G → ℤ) (w : ℤ)
    (hE : ∀ i j c, i ≠ j → i ≠ 0 → j ≠ 0 →
      R i j + P i (j + c) + Q (i + c) j + S (i + c) (j + c) = 0)
    (hVV : ∀ i j, i ≠ j → R i j + R j i = w)
    (hPW : ∀ i g, i ≠ 0 → P i g + Q g i = -w) :
    w = 2 * (R z1 z2 + Q z1 z3 - Q z2 z3 - Q z3 z1 + Q z3 z2 - S z3 z1 + S z3 z2) := by
  have h := certificate_general z1 z2 z3 h12 h13 h23 h1n h2n h3n hsum h2
    R P Q S w hE hVV hPW
  linarith

/-- The Cayley game of `F_2^r` (`r ≥ 2`) has no true refutation of any
length. -/
theorem cayley_f2r_no_refutation {r : ℕ} (hr : 2 ≤ r)
    (w : List (GameClause (Fin r → ZMod 2))) (hw : IsTrueRefutationG w) : False := by
  letI : NeZero r := ⟨by omega⟩
  let zero : Fin r := ⟨0, by omega⟩
  let one : Fin r := ⟨1, by omega⟩
  have h10 : one ≠ zero := by
    intro h
    have hf := congrArg Fin.val h
    norm_num at hf
  let u : Fin r → ZMod 2 := fun i => if i = zero then 1 else 0
  let v : Fin r → ZMod 2 := fun i => if i = one then 1 else 0
  have hu0 : u ≠ 0 := by
    intro h
    have hf := congrFun h zero
    norm_num [u, zero] at hf
  have hv0 : v ≠ 0 := by
    intro h
    have hf := congrFun h one
    norm_num [v, one] at hf
  have huv : u ≠ v := by
    intro h
    have hf := congrFun h one
    norm_num [u, v, one, zero, h10] at hf
  have huz : u ≠ u + v := by
    intro h
    have hf := congrFun h one
    norm_num [u, v, one, zero, h10] at hf
  have hvz : v ≠ u + v := by
    intro h
    have hf := congrFun h zero
    norm_num [u, v, one, zero, h10] at hf
  have hz0 : u + v ≠ 0 := by
    intro h
    have hf := congrFun h zero
    norm_num [u, v, one, zero] at hf
  have h1 : ∀ α j : (Fin r → ZMod 2), Vsum w j + Wsum w (j + α) = 0 := by
    intro α j
    have hred' := altSum_reducible (hw.1 (-α)) j
    have hx'' := altSum_projection w (-α) j
    rw [hx''] at hred'
    simpa [sub_neg_eq_add] using hred'
  obtain ⟨v0, hvW, hvV⟩ := degree1_structure w h1
  have hoddv : Odd v0 := by
    have hwo : Odd (Wsum w 0) := (W0_odd_iff w).mpr hw.2
    have hw0 : Wsum w 0 = -v0 := hvW 0
    have hneg : Odd (-v0) := by simpa [hw0] using hwo
    simpa using (hneg.neg : Odd (-(-v0)))
  have hE' : ∀ i j c : (Fin r → ZMod 2), i ≠ j → i ≠ 0 → j ≠ 0 →
      Rsum w i j + Psum w i (j + c) + Qsum w (i + c) j + Ssum w (i + c) (j + c) = 0 := by
    intro i j c hij hi0 hj0
    exact Eprime w hw.1 i j c hij
  have hVV' : ∀ i j : (Fin r → ZMod 2), i ≠ j → Rsum w i j + Rsum w j i = v0 * v0 := by
    intro i j hij
    rw [VV w i j hij, hvV i, hvV j]
  have hPW' : ∀ i g : (Fin r → ZMod 2), i ≠ 0 → Psum w i g + Qsum w g i = -(v0 * v0) := by
    intro i g hi0
    rw [PW w i g, hvV i, hvW g]
    ring
  have hcert := certificate_general_corollary u v (u + v) huv huz hvz hu0 hv0 hz0 rfl
    pi_zmod2_add_self
    (Rsum w) (Psum w) (Qsum w) (Ssum w) (v0 * v0) hE' hVV' hPW'
  have heven : Even (v0 * v0) := by
    refine ⟨(Rsum w u v + Qsum w u (u + v) - Qsum w v (u + v) - Qsum w (u + v) u +
      Qsum w (u + v) v - Ssum w (u + v) u + Ssum w (u + v) v), ?_⟩
    rw [hcert]
    ring
  have hodd : Odd (v0 * v0) := Odd.mul hoddv hoddv
  exact odd_not_even hodd heven

/-- The Cayley game of `F_2^r` has the standard PREF for every `r`. -/
theorem cayley_f2r_hasPREF (r : ℕ) :
    IsPREFG (G := Fin r → ZMod 2) (standardZG (G := Fin r → ZMod 2)) := by
  exact standardZG_isPREF (G := Fin r → ZMod 2)

/-- For `r ≥ 2`, the Cayley game of `F_2^r` has the standard PREF and no true
refutation of any length. -/
theorem cayley_f2r_hasPREF_and_no_refutation {r : ℕ} (hr : 2 ≤ r) :
    IsPREFG (G := Fin r → ZMod 2) (standardZG (G := Fin r → ZMod 2)) ∧
      ∀ w : List (GameClause (Fin r → ZMod 2)), ¬ IsTrueRefutationG w := by
  constructor
  · exact cayley_f2r_hasPREF r
  · intro w hw
    exact cayley_f2r_no_refutation hr w hw

end FourXOR
end Research
end QIT

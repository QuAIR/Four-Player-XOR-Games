/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public meta import Mathlib.Data.Fintype.Pi

/-!
# Hamming geometry of four-player three-question clauses

An unsigned clause is a word of length four over a three-letter alphabet.
This module records the exact sphere, radius-one ball, and ball-intersection
cardinalities used at the nine- and ten-clause structural boundary.

The cardinality proofs are closed finite computations over the 81-word
universe.  Their statements are independent of any circuit enumeration.
-/

@[expose] public section

namespace QIT
namespace XORGame

/-- The Hamming distance between two four-player, three-question clauses. -/
def hammingDistance (x y : FourByThreeClause) : Nat :=
  (Finset.univ.filter fun coordinate : FourByThreePlayer =>
    x coordinate ≠ y coordinate).card

/-- The clauses at exactly `radius` Hamming coordinates from `center`. -/
def hammingSphere (center : FourByThreeClause) (radius : Nat) :
    Finset FourByThreeClause :=
  Finset.univ.filter fun point => hammingDistance center point = radius

/-- The clauses at Hamming distance at most `radius` from `center`. -/
def closedHammingBall (center : FourByThreeClause) (radius : Nat) :
    Finset FourByThreeClause :=
  Finset.univ.filter fun point => hammingDistance center point ≤ radius

/-- The closed radius-one Hamming ball about a clause. -/
def radiusOneBall (center : FourByThreeClause) : Finset FourByThreeClause :=
  closedHammingBall center 1

/-- There are exactly `3 ^ 4 = 81` unsigned four-player clauses. -/
@[simp]
theorem fourByThreeClause_card :
    Fintype.card FourByThreeClause = 81 := by
  native_decide

/-- A clause has Hamming distance zero from itself. -/
@[simp]
theorem hammingDistance_self (x : FourByThreeClause) :
    hammingDistance x x = 0 := by
  simp [hammingDistance]

/-- Hamming distance is symmetric. -/
theorem hammingDistance_comm (x y : FourByThreeClause) :
    hammingDistance x y = hammingDistance y x := by
  simp only [hammingDistance]
  congr 1
  ext coordinate
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ne_comm

/-- Two four-by-three clauses have distance zero exactly when they coincide. -/
@[simp]
theorem hammingDistance_eq_zero_iff (x y : FourByThreeClause) :
    hammingDistance x y = 0 ↔ x = y := by
  constructor
  · intro h
    have hempty :
        (Finset.univ.filter fun coordinate : FourByThreePlayer =>
          x coordinate ≠ y coordinate) = ∅ :=
      Finset.card_eq_zero.mp h
    apply funext
    intro coordinate
    by_contra hxy
    have hmem :
        coordinate ∈
          (Finset.univ.filter fun i : FourByThreePlayer => x i ≠ y i) := by
      simp [hxy]
    simp [hempty] at hmem
  · rintro rfl
    exact hammingDistance_self x

/-- Four-by-three clauses differ in at most four coordinates. -/
theorem hammingDistance_le_four (x y : FourByThreeClause) :
    hammingDistance x y ≤ 4 := by
  unfold hammingDistance
  calc
    (Finset.univ.filter fun coordinate : FourByThreePlayer =>
        x coordinate ≠ y coordinate).card ≤ Finset.univ.card :=
      Finset.card_le_card (Finset.filter_subset _ _)
    _ = 4 := Fintype.card_fin 4

/--
The five Hamming spheres about any four-by-three clause have cardinalities
`1, 8, 24, 32, 16`.
-/
theorem hammingSphere_card_profile (center : FourByThreeClause) :
    (hammingSphere center 0).card = 1 ∧
      (hammingSphere center 1).card = 8 ∧
      (hammingSphere center 2).card = 24 ∧
      (hammingSphere center 3).card = 32 ∧
      (hammingSphere center 4).card = 16 := by
  exact (by
    native_decide :
      ∀ center : FourByThreeClause,
        (hammingSphere center 0).card = 1 ∧
          (hammingSphere center 1).card = 8 ∧
          (hammingSphere center 2).card = 24 ∧
          (hammingSphere center 3).card = 32 ∧
          (hammingSphere center 4).card = 16) center

/-- The radius-zero Hamming sphere consists only of its center. -/
@[simp]
theorem hammingSphere_zero_card (center : FourByThreeClause) :
    (hammingSphere center 0).card = 1 :=
  (hammingSphere_card_profile center).1

/-- A four-by-three clause has eight Hamming neighbors at distance one. -/
@[simp]
theorem hammingSphere_one_card (center : FourByThreeClause) :
    (hammingSphere center 1).card = 8 :=
  (hammingSphere_card_profile center).2.1

/-- The distance-two Hamming sphere has 24 clauses. -/
@[simp]
theorem hammingSphere_two_card (center : FourByThreeClause) :
    (hammingSphere center 2).card = 24 :=
  (hammingSphere_card_profile center).2.2.1

/-- The distance-three Hamming sphere has 32 clauses. -/
@[simp]
theorem hammingSphere_three_card (center : FourByThreeClause) :
    (hammingSphere center 3).card = 32 :=
  (hammingSphere_card_profile center).2.2.2.1

/-- The distance-four Hamming sphere has 16 clauses. -/
@[simp]
theorem hammingSphere_four_card (center : FourByThreeClause) :
    (hammingSphere center 4).card = 16 :=
  (hammingSphere_card_profile center).2.2.2.2

/-- Every closed radius-one ball in the four-by-three clause space has nine clauses. -/
@[simp]
theorem radiusOneBall_card (center : FourByThreeClause) :
    (radiusOneBall center).card = 9 := by
  exact (by
    native_decide :
      ∀ center : FourByThreeClause, (radiusOneBall center).card = 9) center

/--
Two radius-one balls intersect in `9`, `3`, `2`, or `0` clauses according as
the distance between their centers is `0`, `1`, `2`, or at least `3`.
-/
theorem radiusOneBall_inter_card (x y : FourByThreeClause) :
    (radiusOneBall x ∩ radiusOneBall y).card =
      match hammingDistance x y with
      | 0 => 9
      | 1 => 3
      | 2 => 2
      | _ => 0 := by
  exact (by
    native_decide :
      ∀ x y : FourByThreeClause,
        (radiusOneBall x ∩ radiusOneBall y).card =
          match hammingDistance x y with
          | 0 => 9
          | 1 => 3
          | 2 => 2
          | _ => 0) x y

/-- Coincident centers give a nine-clause intersection. -/
theorem radiusOneBall_inter_card_of_distance_zero
    (x y : FourByThreeClause) (h : hammingDistance x y = 0) :
    (radiusOneBall x ∩ radiusOneBall y).card = 9 := by
  rw [radiusOneBall_inter_card, h]

/-- Centers at distance one give a three-clause intersection. -/
theorem radiusOneBall_inter_card_of_distance_one
    (x y : FourByThreeClause) (h : hammingDistance x y = 1) :
    (radiusOneBall x ∩ radiusOneBall y).card = 3 := by
  rw [radiusOneBall_inter_card, h]

/-- Centers at distance two give a two-clause intersection. -/
theorem radiusOneBall_inter_card_of_distance_two
    (x y : FourByThreeClause) (h : hammingDistance x y = 2) :
    (radiusOneBall x ∩ radiusOneBall y).card = 2 := by
  rw [radiusOneBall_inter_card, h]

/-- Radius-one balls with centers at distance at least three are disjoint. -/
theorem radiusOneBall_inter_card_of_three_le
    (x y : FourByThreeClause) (h : 3 ≤ hammingDistance x y) :
    (radiusOneBall x ∩ radiusOneBall y).card = 0 := by
  rw [radiusOneBall_inter_card]
  generalize hd : hammingDistance x y = distance at h ⊢
  cases distance with
  | zero => simp at h
  | succ distance =>
      cases distance with
      | zero => simp at h
      | succ distance =>
          cases distance with
          | zero => simp at h
          | succ distance => rfl

end XORGame
end QIT

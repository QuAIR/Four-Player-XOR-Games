/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.CombinatorialLifting
import FourXOR.TranslationMatchingOnlyIf

/-!
# FourXOR: the finite-group translation-matching classification

This module packages the translation-matching classification: a finite group admits a common
noncrossing order for its right-translation matchings exactly when it is
cyclic.  Geometric crossing is expressed by the endpoint-order-independent
predicate `ChordCross`; the oriented predicate `Cross` is only used after
normalizing the first chord to start at `E 1` of rank zero.  The only-if
direction rank-compresses an arbitrary order, rotates it so that `E 1` has
rank zero, bridges `ChordCross` back to `Cross`, and reuses the existing
`noncrossing_order_cyclic` core.  The if direction transports the `ZMod n`
zigzag construction through the cyclic-group isomorphism.
-/

set_option maxHeartbeats 800000

open scoped BigOperators

namespace QIT
namespace Research
namespace FourXOR

/-- Geometric crossing of two unoriented chords: the first chord is sorted
before applying the oriented `Cross` predicate. -/
def ChordCross (a b c d : ℕ) : Prop :=
  Cross (min a b) (max a b) c d

/-- A common noncrossing order of all right-translation matchings. -/
def HasCommonNoncrossingOrder
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] : Prop :=
  ∃ p : Point G → ℕ,
    Function.Injective p ∧
      ∀ g x y : G, x ≠ y →
        ¬ ChordCross (p (E x)) (p (O (x * g)))
            (p (E y)) (p (O (y * g)))

/-- `ChordCross` is symmetric under swapping the endpoints of the first
chord. -/
theorem chordCross_swap_left (a b c d : ℕ) :
    ChordCross a b c d ↔ ChordCross b a c d := by
  simp [ChordCross, min_comm, max_comm]

/-- `ChordCross` is symmetric under swapping the endpoints of the second
chord. -/
theorem chordCross_swap_right (a b c d : ℕ) :
    ChordCross a b c d ↔ ChordCross a b d c := by
  unfold ChordCross
  unfold Cross
  omega

/-- `ChordCross` is symmetric under exchanging the two chords. -/
theorem chordCross_swap_chords (a b c d : ℕ) :
    ChordCross a b c d ↔ ChordCross c d a b := by
  unfold ChordCross
  by_cases hab : a ≤ b
  · by_cases hcd : c ≤ d
    · simp [min_eq_left hab, max_eq_right hab, min_eq_left hcd, max_eq_right hcd]
      unfold Cross
      omega
    · have hdc : d ≤ c := le_of_not_ge hcd
      simp [min_eq_left hab, max_eq_right hab, min_eq_right hdc, max_eq_left hdc]
      unfold Cross
      omega
  · have hba : b ≤ a := le_of_not_ge hab
    by_cases hcd : c ≤ d
    · simp [min_eq_right hba, max_eq_left hba, min_eq_left hcd, max_eq_right hcd]
      unfold Cross
      omega
    · have hdc : d ≤ c := le_of_not_ge hcd
      simp [min_eq_right hba, max_eq_left hba, min_eq_right hdc, max_eq_left hdc]
      unfold Cross
      omega

/-- With the first chord already oriented, `ChordCross` is exactly the
oriented `Cross` predicate. -/
theorem chordCross_eq_cross_of_lt {a b c d : ℕ} (hab : a < b) :
    ChordCross a b c d ↔ Cross a b c d := by
  simp [ChordCross, min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab)]

/-- The rank of `x` in the total order induced by `p`: the number of elements
with smaller position. -/
def orderRank {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → ℕ) (x : α) : Fin (Fintype.card α) :=
  ⟨(Finset.univ.filter (fun y => p y < p x)).card, by
    have hx : x ∉ (Finset.univ.filter (fun y => p y < p x)) := by
      simp
    have hsub : (Finset.univ.filter (fun y => p y < p x)) ⊆ Finset.univ.erase x := by
      intro y hy
      exact Finset.mem_erase.mpr ⟨by
        intro hyx
        subst y
        simp at hy, Finset.mem_univ y⟩
    have hcardpos : 0 < Fintype.card α := Finset.card_pos.mpr ⟨x, Finset.mem_univ x⟩
    have hle : (Finset.univ.filter (fun y => p y < p x)).card + 1 ≤
        Fintype.card α := by
      calc
        (Finset.univ.filter (fun y => p y < p x)).card + 1
            ≤ (Finset.univ.erase x).card + 1 := by
              exact Nat.succ_le_succ (Finset.card_le_card hsub)
        _ = Fintype.card α := by
              simp [Finset.card_erase_of_mem (Finset.mem_univ x)]
              omega
    omega⟩

/-- `orderRank` is injective for an injective position function. -/
theorem orderRank_injective {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {p : α → ℕ} (hp : Function.Injective p) :
    Function.Injective (orderRank p) := by
  intro x y h
  have hval : (orderRank p x).val = (orderRank p y).val := congrArg Fin.val h
  simp [orderRank] at hval
  by_contra hne
  have hxy : p x < p y ∨ p y < p x := lt_or_gt_of_ne (by
    intro hEq
    apply hne
    exact hp hEq)
  rcases hxy with hxy | hyx
  · have hsub : (Finset.univ.filter (fun z => p z < p x)) ⊆
        (Finset.univ.filter (fun z => p z < p y)) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        lt_trans (Finset.mem_filter.mp hz).2 hxy⟩
    have hxmem : x ∈ (Finset.univ.filter (fun z => p z < p y)) := by
      simp [hxy]
    have hxnot : x ∉ (Finset.univ.filter (fun z => p z < p x)) := by
      simp
    have hss : (Finset.univ.filter (fun z => p z < p x)) ⊂
        (Finset.univ.filter (fun z => p z < p y)) :=
      ⟨hsub, by intro hts; exact hxnot (hts hxmem)⟩
    have hlt := Finset.card_lt_card hss
    omega
  · have hsub : (Finset.univ.filter (fun z => p z < p y)) ⊆
        (Finset.univ.filter (fun z => p z < p x)) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        lt_trans (Finset.mem_filter.mp hz).2 hyx⟩
    have hymem : y ∈ (Finset.univ.filter (fun z => p z < p x)) := by
      simp [hyx]
    have hynot : y ∉ (Finset.univ.filter (fun z => p z < p y)) := by
      simp
    have hss : (Finset.univ.filter (fun z => p z < p y)) ⊂
        (Finset.univ.filter (fun z => p z < p x)) :=
      ⟨hsub, by intro hts; exact hynot (hts hymem)⟩
    have hlt := Finset.card_lt_card hss
    omega

/-- Rank comparison is position comparison. -/
theorem orderRank_lt_iff {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {p : α → ℕ} (hp : Function.Injective p) (x y : α) :
    (orderRank p x).val < (orderRank p y).val ↔ p x < p y := by
  constructor
  · intro h
    by_contra hnot
    rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hlt | heq
    · have hsub : (Finset.univ.filter (fun z => p z < p y)) ⊆
          (Finset.univ.filter (fun z => p z < p x)) := by
        intro z hz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
          lt_trans (Finset.mem_filter.mp hz).2 hlt⟩
      have hymem : y ∈ (Finset.univ.filter (fun z => p z < p x)) := by
        simp [hlt]
      have hynot : y ∉ (Finset.univ.filter (fun z => p z < p y)) := by
        simp
      have hss : (Finset.univ.filter (fun z => p z < p y)) ⊂
          (Finset.univ.filter (fun z => p z < p x)) :=
        ⟨hsub, by intro hts; exact hynot (hts hymem)⟩
      have hlt' := Finset.card_lt_card hss
      simp [orderRank] at h
      omega
    · simp [orderRank, heq.symm] at h
  · intro hxy
    have hsub : (Finset.univ.filter (fun z => p z < p x)) ⊆
        (Finset.univ.filter (fun z => p z < p y)) := by
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ z,
        lt_trans (Finset.mem_filter.mp hz).2 hxy⟩
    have hxmem : x ∈ (Finset.univ.filter (fun z => p z < p y)) := by
      simp [hxy]
    have hxnot : x ∉ (Finset.univ.filter (fun z => p z < p x)) := by
      simp
    have hss : (Finset.univ.filter (fun z => p z < p x)) ⊂
        (Finset.univ.filter (fun z => p z < p y)) :=
      ⟨hsub, by intro hts; exact hxnot (hts hxmem)⟩
    have hlt := Finset.card_lt_card hss
    simpa [orderRank] using hlt

/-- Crossing is preserved by replacing positions with their ranks. -/
theorem chordCross_orderRank_iff {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (p : α → ℕ) (hp : Function.Injective p) (a b c d : α) :
    ChordCross (orderRank p a).val (orderRank p b).val
        (orderRank p c).val (orderRank p d).val ↔
      ChordCross (p a) (p b) (p c) (p d) := by
  by_cases hab : p a < p b
  · have hrank : (orderRank p a).val < (orderRank p b).val :=
      (orderRank_lt_iff hp a b).2 hab
    unfold ChordCross
    simp [min_eq_left (le_of_lt hab), max_eq_right (le_of_lt hab),
      min_eq_left (le_of_lt hrank), max_eq_right (le_of_lt hrank)]
    unfold Cross
    simp [orderRank_lt_iff hp]
  · by_cases hEq : p a = p b
    · have hab' : a = b := hp hEq
      subst a
      unfold ChordCross
      simp [min_self, max_self]
      unfold Cross
      simp [orderRank_lt_iff hp]
    · have hlt : p b < p a := lt_of_le_of_ne (le_of_not_gt hab) (Ne.symm hEq)
      have hrank : (orderRank p b).val < (orderRank p a).val :=
        (orderRank_lt_iff hp b a).2 hlt
      unfold ChordCross
      simp [min_eq_right (le_of_lt hrank), max_eq_left (le_of_lt hrank),
        min_eq_right (le_of_lt hlt), max_eq_left (le_of_lt hlt)]
      unfold Cross
      simp [orderRank_lt_iff hp]

/-- Modular subtraction by `anchor` on `Fin N`. -/
def rotateRank {N : ℕ} [NeZero N] (anchor x : Fin N) : Fin N :=
  x - anchor

@[simp]
theorem rotateRank_anchor_zero {N : ℕ} [NeZero N] (a : Fin N) :
    rotateRank a a = 0 := by
  simp [rotateRank]

theorem rotateRank_injective {N : ℕ} [NeZero N] (a : Fin N) :
    Function.Injective (rotateRank a) := by
  intro x y h
  have h' : (x - a) + a = (y - a) + a := congrArg (fun z : Fin N => z + a) h
  simpa using h'

/-- The value of a rotated rank, split at the anchor. -/
private lemma rotateRank_val {N : ℕ} [NeZero N] (anchor x : Fin N) :
    (rotateRank anchor x).val =
      if anchor.val ≤ x.val then x.val - anchor.val
      else x.val + N - anchor.val := by
  unfold rotateRank
  have hanchor : anchor.val < N := anchor.isLt
  have hxval : x.val < N := x.isLt
  have hpos : 0 < N := NeZero.pos N
  by_cases h : anchor.val ≤ x.val
  · have hrew : N - anchor.val + x.val = x.val + N - anchor.val := by
      rw [add_comm, Nat.add_sub_assoc (le_of_lt hanchor)]
    have hlt : x.val - anchor.val < N := by omega
    have hmod : (x.val + N - anchor.val) % N = x.val - anchor.val := by
      have hsplit : x.val + N - anchor.val = N + (x.val - anchor.val) := by omega
      rw [hsplit, Nat.add_mod]
      simp [Nat.mod_self, Nat.mod_eq_of_lt hlt]
    have hx' : (x - anchor).val = x.val - anchor.val := by
      rw [Fin.val_sub, hrew, hmod]
    simp [h, hx']
  · have hlt : x.val < anchor.val := Nat.lt_of_not_ge h
    have hsum : N - anchor.val + x.val < N := by omega
    have hmod : (N - anchor.val + x.val) % N = N - anchor.val + x.val := by
      rw [Nat.mod_eq_of_lt hsum]
    have hx' : (x - anchor).val = x.val + N - anchor.val := by
      rw [Fin.val_sub, hmod]
      rw [add_comm, Nat.add_sub_assoc (le_of_lt hanchor)]
    simp [h, hx']

/-- Rotated rank comparison, split into the three cyclic-order cases. -/
private lemma rotateRank_lt_iff {N : ℕ} [NeZero N] (anchor x y : Fin N) :
    (rotateRank anchor x).val < (rotateRank anchor y).val ↔
      (x.val < anchor.val ∧ y.val < anchor.val ∧ x.val < y.val) ∨
        (anchor.val ≤ x.val ∧ anchor.val ≤ y.val ∧ x.val < y.val) ∨
          (anchor.val ≤ x.val ∧ y.val < anchor.val) := by
  rw [rotateRank_val anchor x, rotateRank_val anchor y]
  have hanchor : anchor.val < N := anchor.isLt
  have hxval : x.val < N := x.isLt
  have hyval : y.val < N := y.isLt
  by_cases hx : anchor.val ≤ x.val
  · by_cases hy : anchor.val ≤ y.val
    · simp [hx, hy]
      omega
    · simp [hx, hy]
      omega
  · by_cases hy : anchor.val ≤ y.val
    · simp [hx, hy]
      omega
    · simp [hx, hy]
      omega

/-- Rotated order for two points both before the anchor. -/
private lemma rotateRank_le_of_lt_both_before {N : ℕ} [NeZero N]
    (anchor x y : Fin N) (hx : x.val < anchor.val) (hy : y.val < anchor.val)
    (hxy : x.val < y.val) :
    (rotateRank anchor x).val ≤ (rotateRank anchor y).val :=
  le_of_lt ((rotateRank_lt_iff anchor x y).2 (Or.inl ⟨hx, hy, hxy⟩))

/-- Rotated order for two points both after the anchor. -/
private lemma rotateRank_le_of_lt_both_after {N : ℕ} [NeZero N]
    (anchor x y : Fin N) (hx : ¬ x.val < anchor.val) (hy : ¬ y.val < anchor.val)
    (hxy : x.val < y.val) :
    (rotateRank anchor x).val ≤ (rotateRank anchor y).val := by
  have hx' : anchor.val ≤ x.val := le_of_not_gt hx
  have hy' : anchor.val ≤ y.val := le_of_not_gt hy
  exact le_of_lt ((rotateRank_lt_iff anchor x y).2 (Or.inr (Or.inl ⟨hx', hy', hxy⟩)))

/-- Rotated order for the first point after and the second before the
anchor. -/
private lemma rotateRank_le_of_lt_after_before {N : ℕ} [NeZero N]
    (anchor x y : Fin N) (hx : ¬ x.val < anchor.val) (hy : y.val < anchor.val) :
    (rotateRank anchor x).val ≤ (rotateRank anchor y).val := by
  have hx' : anchor.val ≤ x.val := le_of_not_gt hx
  exact le_of_lt ((rotateRank_lt_iff anchor x y).2 (Or.inr (Or.inr ⟨hx', hy⟩)))

/-- Rotated order for the first point before and the second after the
anchor. -/
private lemma rotateRank_le_of_lt_before_after {N : ℕ} [NeZero N]
    (anchor x y : Fin N) (hx : x.val < anchor.val) (hy : ¬ y.val < anchor.val) :
    (rotateRank anchor y).val ≤ (rotateRank anchor x).val := by
  have hy' : anchor.val ≤ y.val := le_of_not_gt hy
  exact le_of_lt ((rotateRank_lt_iff anchor y x).2 (Or.inr (Or.inr ⟨hy', hx⟩)))

/-- The rotation-invariance step for an already-oriented first chord. -/
private lemma chordCross_rotateRank_iff_of_le {N : ℕ} [NeZero N]
    (a b c d anchor : Fin N)
    (hab : a.val ≤ b.val)
    (hne_ab : a.val ≠ b.val) (hne_ac : a.val ≠ c.val) (hne_ad : a.val ≠ d.val)
    (hne_bc : b.val ≠ c.val) (hne_bd : b.val ≠ d.val) (hne_cd : c.val ≠ d.val) :
    ChordCross a.val b.val c.val d.val ↔
      ChordCross (rotateRank anchor a).val (rotateRank anchor b).val
        (rotateRank anchor c).val (rotateRank anchor d).val := by
  have hlt_ab : a.val < b.val := lt_of_le_of_ne hab hne_ab
  have ha : a.val < N := a.isLt
  have hb : b.val < N := b.isLt
  have hc : c.val < N := c.isLt
  have hd : d.val < N := d.isLt
  unfold ChordCross
  simp [min_eq_left hab, max_eq_right hab]
  by_cases haa : a.val < anchor.val
  · by_cases hbb : b.val < anchor.val
    · have h_ab_le : (rotateRank anchor a).val ≤ (rotateRank anchor b).val :=
        rotateRank_le_of_lt_both_before anchor a b haa hbb hlt_ab
      simp [min_eq_left h_ab_le, max_eq_right h_ab_le]
      by_cases hcc : c.val < anchor.val
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
    · have h_ba_le : (rotateRank anchor b).val ≤ (rotateRank anchor a).val :=
        rotateRank_le_of_lt_before_after anchor a b haa hbb
      simp [min_eq_right h_ba_le, max_eq_left h_ba_le]
      by_cases hcc : c.val < anchor.val
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
  · by_cases hbb : b.val < anchor.val
    · have h_ab_le : (rotateRank anchor a).val ≤ (rotateRank anchor b).val :=
        rotateRank_le_of_lt_after_before anchor a b haa hbb
      simp [min_eq_left h_ab_le, max_eq_right h_ab_le]
      by_cases hcc : c.val < anchor.val
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
    · have h_ab_le : (rotateRank anchor a).val ≤ (rotateRank anchor b).val :=
        rotateRank_le_of_lt_both_after anchor a b haa hbb hlt_ab
      simp [min_eq_left h_ab_le, max_eq_right h_ab_le]
      by_cases hcc : c.val < anchor.val
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
      · by_cases hdd : d.val < anchor.val
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega
        · simp [Cross, rotateRank_lt_iff anchor, haa, hbb, hcc, hdd]
          omega

/-- Geometric crossing is invariant under cyclic rank rotation about an
anchor, for four pairwise-distinct endpoints. -/
theorem chordCross_rotateRank_iff {N : ℕ} [NeZero N]
    (a b c d anchor : Fin N)
    (hdistinct : [a, b, c, d].Pairwise (· ≠ ·)) :
    ChordCross a.val b.val c.val d.val ↔
      ChordCross (rotateRank anchor a).val (rotateRank anchor b).val
        (rotateRank anchor c).val (rotateRank anchor d).val := by
  have hne_ab : a.val ≠ b.val := by
    intro h
    have hne : a ≠ b := (List.pairwise_cons.mp hdistinct).1 b (by simp)
    exact hne (Fin.ext h)
  have hne_ac : a.val ≠ c.val := by
    intro h
    have hne : a ≠ c := (List.pairwise_cons.mp hdistinct).1 c (by simp)
    exact hne (Fin.ext h)
  have hne_ad : a.val ≠ d.val := by
    intro h
    have hne : a ≠ d := (List.pairwise_cons.mp hdistinct).1 d (by simp)
    exact hne (Fin.ext h)
  have hne_bc : b.val ≠ c.val := by
    intro h
    have htail := (List.pairwise_cons.mp hdistinct).2
    have hne : b ≠ c := (List.pairwise_cons.mp htail).1 c (by simp)
    exact hne (Fin.ext h)
  have hne_bd : b.val ≠ d.val := by
    intro h
    have htail := (List.pairwise_cons.mp hdistinct).2
    have hne : b ≠ d := (List.pairwise_cons.mp htail).1 d (by simp)
    exact hne (Fin.ext h)
  have hne_cd : c.val ≠ d.val := by
    intro h
    have htail := (List.pairwise_cons.mp hdistinct).2
    have htail' := (List.pairwise_cons.mp htail).2
    have hne : c ≠ d := (List.pairwise_cons.mp htail').1 d (by simp)
    exact hne (Fin.ext h)
  by_cases hab : a.val ≤ b.val
  · exact chordCross_rotateRank_iff_of_le a b c d anchor hab
      hne_ab hne_ac hne_ad hne_bc hne_bd hne_cd
  · have hba : b.val ≤ a.val := le_of_lt (lt_of_not_ge hab)
    calc
      ChordCross a.val b.val c.val d.val
          ↔ ChordCross b.val a.val c.val d.val := chordCross_swap_left _ _ _ _
      _ ↔ ChordCross (rotateRank anchor b).val (rotateRank anchor a).val
            (rotateRank anchor c).val (rotateRank anchor d).val :=
            chordCross_rotateRank_iff_of_le b a c d anchor hba
              hne_ab.symm hne_bc hne_bd hne_ac hne_ad hne_cd
      _ ↔ ChordCross (rotateRank anchor a).val (rotateRank anchor b).val
            (rotateRank anchor c).val (rotateRank anchor d).val :=
            (chordCross_swap_left _ _ _ _).symm

/-- The four matching endpoints are pairwise distinct for `x ≠ y`. -/
private lemma matching_points_pairwise (G : Type*) [Group G] {x y g : G}
    (hxy : x ≠ y) :
    [E x, O (x * g), E y, O (y * g)].Pairwise (· ≠ ·) := by
  have h1 : E x ≠ O (x * g) := by simp [E, O]
  have h2 : E x ≠ E y := by
    intro h
    exact hxy (Sum.inl.inj h)
  have h3 : E x ≠ O (y * g) := by simp [E, O]
  have h4 : O (x * g) ≠ E y := by simp [E, O]
  have h5 : O (x * g) ≠ O (y * g) := by
    intro h
    exact hxy (mul_right_cancel (Sum.inr.inj h))
  have h6 : E y ≠ O (y * g) := by simp [E, O]
  rw [List.pairwise_cons]
  constructor
  · intro z hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact h1
    · rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact h2
      · rcases List.mem_cons.mp hz with hz | hz
        · subst z
          exact h3
        · simp at hz
  · rw [List.pairwise_cons]
    constructor
    · intro z hz
      rcases List.mem_cons.mp hz with hz | hz
      · subst z
        exact h4
      · rcases List.mem_cons.mp hz with hz | hz
        · subst z
          exact h5
        · simp at hz
    · rw [List.pairwise_cons]
      constructor
      · intro z hz
        rcases List.mem_cons.mp hz with hz | hz
        · subst z
          exact h6
        · simp at hz
      · simp

/-- Any common noncrossing order can be normalized so that `E 1` has rank
zero, preserving geometric noncrossing. -/
lemma normalize_common_order (G : Type*) [Group G] [Fintype G] [DecidableEq G]
    (h : HasCommonNoncrossingOrder G) :
    ∃ p : Point G → ℕ,
      Function.Injective p ∧ p (E 1) = 0 ∧
        ∀ g x y : G, x ≠ y →
          ¬ ChordCross (p (E x)) (p (O (x * g)))
              (p (E y)) (p (O (y * g))) := by
  rcases h with ⟨p0, hp0, hnc0⟩
  letI : Nonempty (Point G) := inferInstance
  let a : Fin (Fintype.card (Point G)) := orderRank p0 (E (1 : G))
  let p : Point G → ℕ := fun pt => (rotateRank a (orderRank p0 pt)).val
  refine ⟨p, ?_, ?_, ?_⟩
  · intro x y hxy
    have h1 : rotateRank a (orderRank p0 x) = rotateRank a (orderRank p0 y) := by
      exact Fin.ext hxy
    have h2 : orderRank p0 x = orderRank p0 y := rotateRank_injective a h1
    exact orderRank_injective hp0 h2
  · simp [p, a, rotateRank_anchor_zero]
  · intro g x y hxy
    intro hcross
    have hcross' : ChordCross (rotateRank a (orderRank p0 (E x))).val
        (rotateRank a (orderRank p0 (O (x * g)))).val
        (rotateRank a (orderRank p0 (E y))).val
        (rotateRank a (orderRank p0 (O (y * g)))).val := by
      simpa [p] using hcross
    have hpts : [E x, O (x * g), E y, O (y * g)].Pairwise (· ≠ ·) :=
      matching_points_pairwise G hxy
    have hranks : [orderRank p0 (E x), orderRank p0 (O (x * g)),
        orderRank p0 (E y), orderRank p0 (O (y * g))].Pairwise (· ≠ ·) := by
      simpa using (List.Pairwise.map (f := orderRank p0)
        (l := [E x, O (x * g), E y, O (y * g)])
        (R := (· ≠ ·)) (S := (· ≠ ·))
        (fun u v huv hEq => huv (orderRank_injective hp0 hEq)) hpts)
    have hcross_ranks : ChordCross (orderRank p0 (E x)).val
        (orderRank p0 (O (x * g))).val
        (orderRank p0 (E y)).val (orderRank p0 (O (y * g))).val := by
      exact (chordCross_rotateRank_iff (orderRank p0 (E x))
        (orderRank p0 (O (x * g))) (orderRank p0 (E y))
        (orderRank p0 (O (y * g))) a hranks).2 hcross'
    have hcross_pos : ChordCross (p0 (E x)) (p0 (O (x * g)))
        (p0 (E y)) (p0 (O (y * g))) := by
      exact (chordCross_orderRank_iff p0 hp0 (E x) (O (x * g)) (E y) (O (y * g))).1
        hcross_ranks
    exact hnc0 g x y hxy hcross_pos

/-- From a normalized geometric common order, the oriented star noncrossing
hypothesis required by `noncrossing_order_cyclic` follows. -/
lemma normalized_chord_noncrossing_implies_star (G : Type*) [Group G]
    [Fintype G] [DecidableEq G]
    (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x y : G, x ≠ y →
      ¬ ChordCross (p (E x)) (p (O (x * g)))
          (p (E y)) (p (O (y * g)))) :
    ∀ g x : G, x ≠ 1 →
      ¬ Cross (p (E 1)) (p (O g))
          (p (E x)) (p (O (x * g))) := by
  intro g x hx
  have hnc' := hnc g 1 x (Ne.symm hx)
  have hnc'' : ¬ ChordCross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))) := by
    simpa using hnc'
  have hlt : p (E 1) < p (O g) := by
    rw [hfirst]
    have hne : p (O g) ≠ 0 := by
      intro h
      have hEq : O g = E (1 : G) := hp (by simpa [hfirst] using h)
      exact (nomatch hEq)
    omega
  intro hcross
  exact hnc'' ((chordCross_eq_cross_of_lt (a := p (E 1)) (b := p (O g))
    (c := p (E x)) (d := p (O (x * g))) hlt).2 hcross)

/-- A common noncrossing order forces the group to be cyclic. -/
theorem commonNoncrossingOrder_implies_isCyclic (G : Type*) [Group G]
    [Fintype G] [DecidableEq G]
    (h : HasCommonNoncrossingOrder G) : IsCyclic G := by
  rcases normalize_common_order G h with ⟨p, hp, hfirst, hnc⟩
  exact noncrossing_order_cyclic p hp hfirst
    (normalized_chord_noncrossing_implies_star G p hp hfirst hnc)

/-- `a` occurs in `word` at index `i`. -/
def OccursAt {α : Type*} (word : List α) (a : α) (i : ℕ) : Prop :=
  ∃ hi : i < word.length, word[i]'hi = a

/-- Every pair of distinct letters that each occur exactly twice has its two
occurrences noncrossing: the occurrence intervals do not alternate. -/
def PairwiseNoncrossingEqualPairs {α : Type*} (word : List α) : Prop :=
  ∀ a b i j k l,
    a ≠ b → i < j → k < l →
    OccursAt word a i → OccursAt word a j →
    OccursAt word b k → OccursAt word b l →
    ¬ Cross i j k l

/-- `OccursAt` is exactly `getElem? = some`. -/
private lemma occursAt_iff_getElem? {α : Type*} {l : List α} {a : α} {i : ℕ} :
    OccursAt l a i ↔ l[i]? = some a := by
  unfold OccursAt
  constructor
  · rintro ⟨hi, hget⟩
    rw [List.getElem?_eq_getElem hi, hget]
  · intro h
    by_cases hi : i < l.length
    · rw [List.getElem?_eq_getElem hi] at h
      exact ⟨hi, Option.some.inj h⟩
    · have hn : l[i]? = none := by simp [hi]
      rw [hn] at h
      simp at h

private lemma occursAt_append_left {α : Type*} {l r : List α} {a : α} {i : ℕ}
    (h : OccursAt l a i) : OccursAt (l ++ r) a i := by
  exact (occursAt_iff_getElem?).2 (by
    rw [List.getElem?_append]
    rcases h with ⟨hi, hget⟩
    simp [hi]
    exact hget)

private lemma occursAt_append_right {α : Type*} {l r : List α} {a : α} {i : ℕ}
    (h : OccursAt r a i) : OccursAt (l ++ r) a (l.length + i) := by
  exact (occursAt_iff_getElem?).2 (by
    rw [List.getElem?_append]
    have hne : ¬ l.length + i < l.length := by omega
    simp [hne]
    exact occursAt_iff_getElem?.1 h)

private lemma occursAt_cons_zero {α : Type*} {x : α} {l : List α} :
    OccursAt (x :: l) x 0 := by
  exact (occursAt_iff_getElem?).2 (by simp)

private lemma occursAt_cons_succ {α : Type*} {x : α} {l : List α} {a : α} {i : ℕ}
    (h : OccursAt l a i) : OccursAt (x :: l) a (i + 1) := by
  exact (occursAt_iff_getElem?).2 (by
    rw [List.getElem?_cons_succ]
    exact occursAt_iff_getElem?.1 h)

private lemma getElem?_singleton_eq_some {α : Type*} {x : α} {t : ℕ} :
    [x][t]? = some x → t = 0 := by
  by_cases ht : t = 0
  · intro; exact ht
  · intro h
    have hpos : 0 < t := Nat.pos_of_ne_zero ht
    have ht' : t = (t - 1) + 1 := by omega
    rw [ht', List.getElem?_cons_succ] at h
    simp at h

private lemma count_cons_mid_of_eq {α : Type*} [DecidableEq α] {x : α} {mid : List α} :
    (x :: mid ++ [x]).count x = 2 + mid.count x := by
  simp
  omega

private lemma count_cons_mid_of_ne {α : Type*} [DecidableEq α] {x c : α} {mid : List α}
    (hc : c ≠ x) : (x :: mid ++ [x]).count c = mid.count c := by
  have hx : ¬ (x == c) = true := by
    intro h'
    have hEq : x = c := LawfulBEq.eq_of_beq (a := x) (b := c) h'
    exact hc hEq.symm
  simp [List.count_cons, List.count_append, hx]

/-- In `x :: mid ++ [x]` with `x ∉ mid`, the outer letter `x` occurs exactly
at indices `0` and `mid.length + 1`. -/
private lemma occursAt_pair_outer {α : Type*} [DecidableEq α] {x : α} {mid : List α}
    (hxnot : x ∉ mid) {i : ℕ} (h : OccursAt (x :: mid ++ [x]) x i) :
    i = 0 ∨ i = mid.length + 1 := by
  rcases h with ⟨hi, hget⟩
  by_cases hi0 : i = 0
  · left; exact hi0
  · right
    have hpos : 0 < i := Nat.pos_of_ne_zero hi0
    have hq : (x :: mid ++ [x])[i]? = some x := occursAt_iff_getElem?.1 ⟨hi, hget⟩
    have hstep : (x :: mid ++ [x])[i]? = (mid ++ [x])[i - 1]? := by
      have hi' : i = (i - 1) + 1 := by omega
      conv_lhs => rw [hi']
      exact List.getElem?_cons_succ (a := x) (l := mid ++ [x]) (i := i - 1)
    rw [hstep] at hq
    have hlt : i - 1 < (mid ++ [x]).length := by
      have hword : i < (x :: mid ++ [x]).length := hi
      simp [List.length_cons, List.length_append] at hword ⊢
      omega
    have hlen : (mid ++ [x]).length = mid.length + 1 := by simp
    by_cases hmid : i - 1 < mid.length
    · have hm : mid[i - 1]'(hmid) = x := by
        rw [List.getElem?_append] at hq
        rw [if_pos hmid] at hq
        rw [List.getElem?_eq_getElem hmid] at hq
        exact Option.some.inj hq
      have hmem : x ∈ mid := by
        exact (List.mem_iff_getElem).2 ⟨i - 1, hmid, hm⟩
      exact False.elim (hxnot hmem)
    · have hge : mid.length ≤ i - 1 := le_of_not_gt hmid
      have heq : i - 1 = mid.length := by omega
      have hxq : (mid ++ [x])[i - 1]? = some x := by
        rw [List.getElem?_append]
        rw [if_neg hmid]
        simp [heq]
      rw [hxq] at hq
      omega

/-- In `x :: mid ++ [x]`, a letter other than `x` occurs in `mid` with the
index shifted down by one. -/
private lemma occursAt_pair_inner {α : Type*} [DecidableEq α] {x : α} {mid : List α}
    {b : α} (hb : b ≠ x) {i : ℕ} (h : OccursAt (x :: mid ++ [x]) b i) :
    0 < i ∧ ∃ hi : i - 1 < mid.length, OccursAt mid b (i - 1) := by
  rcases h with ⟨hi, hget⟩
  have hpos : 0 < i := by
    by_contra hnot
    have hi0 : i = 0 := Nat.eq_zero_of_not_pos hnot
    subst i
    have hz : (x :: mid ++ [x])[0]'(hi) = x := List.getElem_cons_zero x (mid ++ [x]) hi
    exact hb (hget.symm.trans hz)
  have hq : (x :: mid ++ [x])[i]? = some b := occursAt_iff_getElem?.1 ⟨hi, hget⟩
  have hstep : (x :: mid ++ [x])[i]? = (mid ++ [x])[i - 1]? := by
    have hi' : i = (i - 1) + 1 := by omega
    conv_lhs => rw [hi']
    exact List.getElem?_cons_succ (a := x) (l := mid ++ [x]) (i := i - 1)
  rw [hstep] at hq
  have hlt : i - 1 < (mid ++ [x]).length := by
    have hword : i < (x :: mid ++ [x]).length := hi
    simp [List.length_cons, List.length_append] at hword ⊢
    omega
  have hlen : (mid ++ [x]).length = mid.length + 1 := by simp
  by_cases hmid : i - 1 < mid.length
  · have hm : mid[i - 1]'(hmid) = b := by
      rw [List.getElem?_append] at hq
      rw [if_pos hmid] at hq
      rw [List.getElem?_eq_getElem hmid] at hq
      exact Option.some.inj hq
    exact ⟨hpos, hmid, ⟨hmid, hm⟩⟩
  · have hge : mid.length ≤ i - 1 := le_of_not_gt hmid
    have heq : i - 1 = mid.length := by omega
    have hxq : (mid ++ [x])[i - 1]? = some x := by
      rw [List.getElem?_append]
      rw [if_neg hmid]
      simp [heq]
    rw [hxq] at hq
    exact False.elim (hb (Option.some.inj hq).symm)

private lemma cross_add_const (a b c d k : ℕ) :
    Cross (a + k) (b + k) (c + k) (d + k) ↔ Cross a b c d := by
  unfold Cross
  omega

private lemma occursAt_classify_append {α : Type*} {l r : List α} {a : α} {i : ℕ}
    (h : OccursAt (l ++ r) a i) :
    (i < l.length ∧ OccursAt l a i) ∨
      (l.length ≤ i ∧ OccursAt r a (i - l.length)) := by
  rcases h with ⟨hi, hget⟩
  have hq : (l ++ r)[i]? = some a := occursAt_iff_getElem?.1 ⟨hi, hget⟩
  rw [List.getElem?_append] at hq
  by_cases hlt : i < l.length
  · left
    constructor
    · exact hlt
    · exact occursAt_iff_getElem?.2 (by rw [if_pos hlt] at hq; exact hq)
  · right
    have hge : l.length ≤ i := le_of_not_gt hlt
    constructor
    · exact hge
    · exact occursAt_iff_getElem?.2 (by rw [if_neg hlt] at hq; exact hq)

private lemma cross_sub_const (a b c d k : ℕ)
    (hka : k ≤ a) (hkb : k ≤ b) (hkc : k ≤ c) (hkd : k ≤ d) :
    Cross (a - k) (b - k) (c - k) (d - k) ↔ Cross a b c d := by
  unfold Cross
  omega

private lemma occursAt_append_of_count_left {α : Type*} [DecidableEq α]
    {l r : List α} {c : α} {i : ℕ}
    (hrc : r.count c = 0) (h : OccursAt (l ++ r) c i) :
    i < l.length ∧ OccursAt l c i := by
  rcases occursAt_classify_append h with hleft | hright
  · exact hleft
  · exfalso
    have hmem : c ∈ r := by
      rcases hright.2 with ⟨hlt, hget⟩
      exact hget.symm ▸ List.getElem_mem hlt
    have hpos : 0 < r.count c := List.count_pos_iff.mpr hmem
    omega

private lemma occursAt_append_of_count_right {α : Type*} [DecidableEq α]
    {l r : List α} {c : α} {i : ℕ}
    (hlc : l.count c = 0) (h : OccursAt (l ++ r) c i) :
    l.length ≤ i ∧ OccursAt r c (i - l.length) := by
  rcases occursAt_classify_append h with hleft | hright
  · exfalso
    have hmem : c ∈ l := by
      rcases hleft.2 with ⟨hlt, hget⟩
      exact hget.symm ▸ List.getElem_mem hlt
    have hpos : 0 < l.count c := List.count_pos_iff.mpr hmem
    omega
  · exact hright

/-- An occurrence in a concatenation lies in the side whose count is two. -/
private lemma occursAt_append_side {α : Type*} [DecidableEq α]
    {l r : List α} {c : α} {i : ℕ}
    (hlc : l.count c = 0 ∨ l.count c = 2)
    (hrc : r.count c = 0 ∨ r.count c = 2)
    (htot : l.count c + r.count c = 0 ∨ l.count c + r.count c = 2)
    (h : OccursAt (l ++ r) c i) :
    (l.count c = 2 ∧ r.count c = 0 ∧ i < l.length ∧ OccursAt l c i) ∨
      (l.count c = 0 ∧ r.count c = 2 ∧ l.length ≤ i ∧ OccursAt r c (i - l.length)) := by
  rcases hlc with hl0 | hl2
  · rcases hrc with hr0 | hr2
    · exfalso
      rcases occursAt_classify_append h with hleft | hright
      · have hmem : c ∈ l := by
          rcases hleft.2 with ⟨hlt, hget⟩
          exact hget.symm ▸ List.getElem_mem hlt
        have hpos : 0 < l.count c := List.count_pos_iff.mpr hmem
        omega
      · have hmem : c ∈ r := by
          rcases hright.2 with ⟨hlt, hget⟩
          exact hget.symm ▸ List.getElem_mem hlt
        have hpos : 0 < r.count c := List.count_pos_iff.mpr hmem
        omega
    · right
      rcases occursAt_classify_append h with hleft | hright
      · exfalso
        have hmem : c ∈ l := by
          rcases hleft.2 with ⟨hlt, hget⟩
          exact hget.symm ▸ List.getElem_mem hlt
        have hpos : 0 < l.count c := List.count_pos_iff.mpr hmem
        omega
      · exact ⟨hl0, hr2, hright.1, hright.2⟩
  · rcases hrc with hr0 | hr2
    · left
      rcases occursAt_classify_append h with hleft | hright
      · exact ⟨hl2, hr0, hleft.1, hleft.2⟩
      · exfalso
        have hmem : c ∈ r := by
          rcases hright.2 with ⟨hlt, hget⟩
          exact hget.symm ▸ List.getElem_mem hlt
        have hpos : 0 < r.count c := List.count_pos_iff.mpr hmem
        omega
    · exfalso
      rcases htot with h0 | h2 <;> omega

/-- In a nested word, every letter occurs an even number of times. -/
theorem NestedWord.count_even {α : Type*} [DecidableEq α] {word : List α}
    (hnested : NestedWord word) (a : α) : Even (word.count a) := by
  induction hnested with
  | nil => simp
  | pair x mid hmid ih =>
      have hlast : [x].count a = if (x == a) = true then 1 else 0 := by
        rw [List.count_cons]
        simp
      have ht : Even ((if (x == a) = true then 1 else 0) +
          (if (x == a) = true then 1 else 0)) := by
        by_cases hx : (x == a) = true <;> simp [hx]
      simpa [List.count_cons, List.count_append, hlast, add_assoc] using
        (Even.add ih ht)
  | @concat l r hl hr ihl ihr =>
      simpa [List.count_append] using Even.add ihl ihr

/-- In a nested word whose letters each occur zero or two times, the occurrence
intervals of distinct letters are pairwise noncrossing. -/
theorem NestedWord.equalPairs_noncrossing {α : Type*} [DecidableEq α] {word : List α}
    (hnested : NestedWord word)
    (htwice : ∀ a, word.count a = 0 ∨ word.count a = 2) :
    PairwiseNoncrossingEqualPairs word := by
  revert htwice
  induction hnested with
  | nil =>
      intro htwice
      intro a b i j k m hab hij hkm hia hja hkb hmb
      rcases hia with ⟨hi, _⟩
      simp at hi
  | pair x mid hmid ih =>
      intro htwice
      have htwice_mid : ∀ c : α, mid.count c = 0 ∨ mid.count c = 2 := by
        intro c
        by_cases hc : c = x
        · subst c
          rcases htwice x with h0 | h2
          · have hsum : 2 + mid.count x = 0 := by
              simpa [count_cons_mid_of_eq] using h0
            omega
          · have hsum : 2 + mid.count x = 2 := by
              simpa [count_cons_mid_of_eq] using h2
            left
            omega
        · have hcount : (x :: mid ++ [x]).count c = mid.count c :=
            count_cons_mid_of_ne hc
          rcases htwice c with h0 | h2
          · left
            simpa [← hcount] using h0
          · right
            simpa [← hcount] using h2
      have hinner : PairwiseNoncrossingEqualPairs mid := ih htwice_mid
      have hxnot : x ∉ mid := by
        intro hmem
        have hpos : 0 < mid.count x := List.count_pos_iff.mpr hmem
        rcases htwice x with h0 | h2
        · have hsum : 2 + mid.count x = 0 := by
            simpa [count_cons_mid_of_eq] using h0
          omega
        · have hsum : 2 + mid.count x = 2 := by
            simpa [count_cons_mid_of_eq] using h2
          omega
      intro a b i j k m hab hij hkm hia hja hkb hmb
      by_cases hane : a = x
      · subst a
        have hbne : b ≠ x := by
          intro hb
          exact hab hb.symm
        rcases occursAt_pair_outer hxnot hia with hi0 | hiL
        · subst i
          rcases occursAt_pair_outer hxnot hja with hj0 | hjL
          · exfalso
            omega
          · subst j
            rcases occursAt_pair_inner hbne hkb with ⟨hkpos, hklt, hkb'⟩
            rcases occursAt_pair_inner hbne hmb with ⟨hmpos, hmlt, hmb'⟩
            intro hcross
            unfold Cross at hcross
            omega
        · subst i
          rcases occursAt_pair_outer hxnot hja with hj0 | hjL
          · exfalso
            omega
          · exfalso
            omega
      · by_cases hbx : b = x
        · subst b
          have hane' : a ≠ x := hane
          rcases occursAt_pair_inner hane' hia with ⟨hipos, hilt, hia'⟩
          rcases occursAt_pair_inner hane' hja with ⟨hjpos, hjlt, hja'⟩
          rcases occursAt_pair_outer hxnot hkb with hk0 | hkL
          · subst k
            rcases occursAt_pair_outer hxnot hmb with hm0 | hmL
            · exfalso
              omega
            · subst m
              intro hcross
              unfold Cross at hcross
              omega
          · subst k
            rcases occursAt_pair_outer hxnot hmb with hm0 | hmL
            · exfalso
              omega
            · exfalso
              omega
        · rcases occursAt_pair_inner hane hia with ⟨hipos, hilt, hia'⟩
          rcases occursAt_pair_inner hane hja with ⟨hjpos, hjlt, hja'⟩
          rcases occursAt_pair_inner hbx hkb with ⟨hkpos, hklt, hkb'⟩
          rcases occursAt_pair_inner hbx hmb with ⟨hmpos, hmlt, hmb'⟩
          have hij' : i - 1 < j - 1 := by omega
          have hkm' : k - 1 < m - 1 := by omega
          have hinner' : ¬ Cross (i - 1) (j - 1) (k - 1) (m - 1) :=
            hinner a b (i - 1) (j - 1) (k - 1) (m - 1) hab hij' hkm' hia' hja' hkb' hmb'
          intro hcross
          exact hinner' ((cross_sub_const i j k m 1 hipos hjpos hkpos hmpos).2 hcross)
  | @concat l r hl hr ihl ihr =>
      intro htwice
      have htwice_l : ∀ c : α, l.count c = 0 ∨ l.count c = 2 := by
        intro c
        have hle : Even (l.count c) := NestedWord.count_even hl c
        rcases htwice c with h0 | h2
        · left
          have hsum : l.count c + r.count c = 0 := by
            simpa [List.count_append] using h0
          omega
        · have hsum : l.count c + r.count c = 2 := by
            simpa [List.count_append] using h2
          rcases (even_iff_two_dvd.mp hle) with ⟨m, hm⟩
          have hm_cases : m = 0 ∨ m = 1 := by omega
          rcases hm_cases with hm0 | hm1
          · left
            omega
          · right
            omega
      have htwice_r : ∀ c : α, r.count c = 0 ∨ r.count c = 2 := by
        intro c
        have hre : Even (r.count c) := NestedWord.count_even hr c
        rcases htwice c with h0 | h2
        · left
          have hsum : l.count c + r.count c = 0 := by
            simpa [List.count_append] using h0
          omega
        · have hsum : l.count c + r.count c = 2 := by
            simpa [List.count_append] using h2
          rcases (even_iff_two_dvd.mp hre) with ⟨m, hm⟩
          have hm_cases : m = 0 ∨ m = 1 := by omega
          rcases hm_cases with hm0 | hm1
          · left
            omega
          · right
            omega
      have hinner_l : PairwiseNoncrossingEqualPairs l := ihl htwice_l
      have hinner_r : PairwiseNoncrossingEqualPairs r := ihr htwice_r
      intro a b i j k m hab hij hkm hia hja hkb hmb
      have htot_a : l.count a + r.count a = 0 ∨ l.count a + r.count a = 2 := by
        rcases htwice a with h0 | h2
        · left
          simpa [List.count_append] using h0
        · right
          simpa [List.count_append] using h2
      have htot_b : l.count b + r.count b = 0 ∨ l.count b + r.count b = 2 := by
        rcases htwice b with h0 | h2
        · left
          simpa [List.count_append] using h0
        · right
          simpa [List.count_append] using h2
      rcases occursAt_append_side (htwice_l a) (htwice_r a) htot_a hia with hia_l | hia_r
      · rcases occursAt_append_side (htwice_l b) (htwice_r b) htot_b hkb with hkb_l | hkb_r
        · rcases hia_l with ⟨hla2, hra0, hlt_i, hia_l'⟩
          rcases hkb_l with ⟨hlb2, hrb0, hlt_k, hkb_l'⟩
          have hja_l' : j < l.length ∧ OccursAt l a j :=
            occursAt_append_of_count_left hra0 hja
          have hmb_l' : m < l.length ∧ OccursAt l b m :=
            occursAt_append_of_count_left hrb0 hmb
          exact hinner_l a b i j k m hab hij hkm hia_l' hja_l'.2 hkb_l' hmb_l'.2
        · rcases hia_l with ⟨hla2, hra0, hlt_i, hia_l'⟩
          rcases hkb_r with ⟨hlb0, hrb2, hge_k, hkb_r'⟩
          have hja_l' : j < l.length ∧ OccursAt l a j :=
            occursAt_append_of_count_left hra0 hja
          have hmb_r' : l.length ≤ m ∧ OccursAt r b (m - l.length) :=
            occursAt_append_of_count_right hlb0 hmb
          rcases hmb_r' with ⟨hge_m, hmb_r''⟩
          intro hcross
          unfold Cross at hcross
          omega
      · rcases occursAt_append_side (htwice_l b) (htwice_r b) htot_b hkb with hkb_l | hkb_r
        · rcases hia_r with ⟨hla0, hra2, hge_i, hia_r'⟩
          rcases hkb_l with ⟨hlb2, hrb0, hlt_k, hkb_l'⟩
          have hja_r' : l.length ≤ j ∧ OccursAt r a (j - l.length) :=
            occursAt_append_of_count_right hla0 hja
          have hmb_l' : m < l.length ∧ OccursAt l b m :=
            occursAt_append_of_count_left hrb0 hmb
          intro hcross
          unfold Cross at hcross
          omega
        · rcases hia_r with ⟨hla0, hra2, hge_i, hia_r'⟩
          rcases hkb_r with ⟨hlb0, hrb2, hge_k, hkb_r'⟩
          have hja_r' : l.length ≤ j ∧ OccursAt r a (j - l.length) :=
            occursAt_append_of_count_right hla0 hja
          have hmb_r' : l.length ≤ m ∧ OccursAt r b (m - l.length) :=
            occursAt_append_of_count_right hlb0 hmb
          rcases hja_r' with ⟨hge_j, hja_r''⟩
          rcases hmb_r' with ⟨hge_m, hmb_r''⟩
          have hij' : i - l.length < j - l.length := by omega
          have hkm' : k - l.length < m - l.length := by omega
          intro hcross
          have hcross' :
              Cross (i - l.length) (j - l.length) (k - l.length) (m - l.length) :=
            (cross_sub_const i j k m l.length hge_i hge_j hge_k hge_m).2 hcross
          exact hinner_r a b (i - l.length) (j - l.length) (k - l.length) (m - l.length)
            hab hij' hkm' hia_r' hja_r'' hkb_r' hmb_r'' hcross'

/-- The zigzag projection is a nested word. -/
theorem projectionZigzag_nested {n : ℕ} (a : ZMod n) [NeZero n] :
    NestedWord (projectionZigzag (n := n) a) := by
  rw [projectionZigzag_split]
  exact NestedWord.concat (blockProj_nested (n := n) 0 (a.val + 1))
    (blockProj_nested (n := n) (a.val + 1) n)

private lemma range_append_add (n m : ℕ) (hm : m ≤ n) :
    List.range n = List.range m ++ (List.range (n - m)).map (fun t => m + t) := by
  induction n generalizing m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst m
      simp
  | succ n ih =>
      by_cases hmn : m = n + 1
      · subst m
        simp
      · have hmle : m ≤ n := by omega
        have hih := ih m hmle
        rw [List.range_succ, hih]
        have hsub : n + 1 - m = (n - m) + 1 := by omega
        rw [hsub, List.range_succ]
        have hmadd : m + (n - m) = n := Nat.add_sub_of_le hmle
        simp [List.map_append, hmadd]

private lemma range_split (n m : ℕ) (hm : m < n) :
    List.range n = List.range m ++ [m] ++
      (List.range (n - m - 1)).map (fun t => m + 1 + t) := by
  have hm1 : m + 1 ≤ n := by omega
  have h := range_append_add n (m + 1) hm1
  rw [h]
  have hsub : n - (m + 1) = n - m - 1 := by omega
  rw [hsub]
  have hrange : List.range (m + 1) = List.range m ++ [m] := by
    rw [List.range_succ]
  rw [hrange]

private lemma flatMap_pair_length {α : Type*} (l : List ℕ) (f g : ℕ → α) :
    (l.flatMap (fun t => [f t, g t])).length = 2 * l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.length_append, ih]
      simp
      omega

private lemma count_interleaving {α : Type*} [BEq α] [LawfulBEq α]
    {l : List ℕ} (f g : ℕ → α) (q : α) :
    (l.flatMap (fun t : ℕ => [f t, g t])).count q =
      (l.map f).count q + (l.map g).count q := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.flatMap_cons, List.count_append, ih]
      simp [List.count_cons, add_assoc, add_comm, add_left_comm]

private lemma count_range_natCast_one {n : ℕ} [NeZero n] (q : ZMod n) :
    ((List.range n).map (fun t : ℕ => (t : ZMod n))).count q = 1 := by
  have hmem : q ∈ (List.range n).map (fun t : ℕ => (t : ZMod n)) := by
    rw [List.mem_map]
    refine ⟨q.val, ?_, ?_⟩
    · simp [q.val_lt]
    · exact ZMod.natCast_zmod_val q
  have hnodup : ((List.range n).map (fun t : ℕ => (t : ZMod n))).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro x hx y hy hxy
    have hxlt : x < n := by simpa using hx
    have hylt : y < n := by simpa using hy
    have hxv : (x : ZMod n).val = x := ZMod.val_natCast_of_lt hxlt
    have hyv : (y : ZMod n).val = y := ZMod.val_natCast_of_lt hylt
    have h : x = y := by
      simpa [hxv, hyv] using congrArg ZMod.val hxy
    exact h
  exact List.count_eq_one_of_mem hnodup hmem

private lemma count_range_neg_add_one {n : ℕ} [NeZero n] (a q : ZMod n) :
    ((List.range n).map (fun t : ℕ => -((t : ZMod n)) + a)).count q = 1 := by
  have hmem : q ∈ (List.range n).map (fun t : ℕ => -((t : ZMod n)) + a) := by
    rw [List.mem_map]
    refine ⟨(a - q).val, ?_, ?_⟩
    · simp [(a - q).val_lt]
    · rw [ZMod.natCast_zmod_val]
      abel
  have hnodup : ((List.range n).map (fun t : ℕ => -((t : ZMod n)) + a)).Nodup := by
    rw [List.nodup_map_iff_inj_on List.nodup_range]
    intro x hx y hy hxy
    have hxlt : x < n := by simpa using hx
    have hylt : y < n := by simpa using hy
    have hneg : -((x : ZMod n)) = -((y : ZMod n)) := by
      exact add_right_cancel hxy
    have hxy' : (x : ZMod n) = (y : ZMod n) := neg_injective hneg
    have hxv : (x : ZMod n).val = x := ZMod.val_natCast_of_lt hxlt
    have hyv : (y : ZMod n).val = y := ZMod.val_natCast_of_lt hylt
    have h : x = y := by
      simpa [hxv, hyv] using congrArg ZMod.val hxy'
    exact h
  exact List.count_eq_one_of_mem hnodup hmem

private lemma flatMap_pair_getElem? {n : ℕ} [NeZero n] (a x : ZMod n) :
    ((List.range n).flatMap (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + a]))[2 * x.val]? =
      some x := by
  have hx : x.val < n := x.val_lt
  have hsplit := range_split n x.val hx
  rw [hsplit]
  rw [List.flatMap_append, List.flatMap_append]
  rw [List.flatMap_singleton, ZMod.natCast_zmod_val]
  have hpre : ((List.range x.val).flatMap
      (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + a])).length = 2 * x.val := by
    simpa using flatMap_pair_length (List.range x.val)
      (fun t : ℕ => (t : ZMod n)) (fun t : ℕ => -((t : ZMod n)) + a)
  rw [List.getElem?_append]
  have hlt : 2 * x.val <
      ((List.range x.val).flatMap (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + a]) ++
        [x, -x + a]).length := by
    simp [hpre]
  rw [if_pos hlt]
  rw [List.getElem?_append]
  have hnot : ¬ 2 * x.val <
      ((List.range x.val).flatMap (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + a])).length := by
    rw [hpre]
    omega
  rw [if_neg hnot]
  simp [hpre, ZMod.natCast_zmod_val]

private lemma flatMap_pair_snd_getElem? {n : ℕ} [NeZero n] (a t : ZMod n) :
    ((List.range n).flatMap (fun s : ℕ => [((s : ZMod n)), -((s : ZMod n)) + a]))[2 * t.val + 1]? =
      some (-t + a) := by
  have ht : t.val < n := t.val_lt
  have hsplit := range_split n t.val ht
  rw [hsplit]
  rw [List.flatMap_append, List.flatMap_append]
  rw [List.flatMap_singleton, ZMod.natCast_zmod_val]
  have hpre : ((List.range t.val).flatMap
      (fun s : ℕ => [((s : ZMod n)), -((s : ZMod n)) + a])).length = 2 * t.val := by
    simpa using flatMap_pair_length (List.range t.val)
      (fun s : ℕ => (s : ZMod n)) (fun s : ℕ => -((s : ZMod n)) + a)
  rw [List.getElem?_append]
  have hlt : 2 * t.val + 1 <
      ((List.range t.val).flatMap (fun s : ℕ => [((s : ZMod n)), -((s : ZMod n)) + a]) ++
        [t, -t + a]).length := by
    simp [hpre]
  rw [if_pos hlt]
  rw [List.getElem?_append]
  have hnot : ¬ 2 * t.val + 1 <
      ((List.range t.val).flatMap (fun s : ℕ => [((s : ZMod n)), -((s : ZMod n)) + a])).length := by
    rw [hpre]
    omega
  rw [if_neg hnot]
  simp [hpre]

/-- In the zigzag projection, every letter occurs exactly twice. -/
theorem projectionZigzag_count_eq_two {n : ℕ} (a q : ZMod n) [NeZero n] :
    (projectionZigzag (n := n) a).count q = 2 := by
  unfold projectionZigzag
  rw [count_interleaving (f := fun t : ℕ => (t : ZMod n))
      (g := fun t : ℕ => -((t : ZMod n)) + a) q]
  rw [count_range_natCast_one, count_range_neg_add_one]

/-- In the zigzag projection, the letter `x` occurs at the even index
`2 * x.val`. -/
lemma projectionZigzag_occurs_E {n : ℕ} (a x : ZMod n) [NeZero n] :
    OccursAt (projectionZigzag (n := n) a) x (2 * x.val) := by
  rw [occursAt_iff_getElem?]
  unfold projectionZigzag
  exact flatMap_pair_getElem? a x

/-- In the zigzag projection, the letter `y + a` occurs at the odd index
`2 * (-y).val + 1`. -/
lemma projectionZigzag_occurs_O {n : ℕ} (a y : ZMod n) [NeZero n] :
    OccursAt (projectionZigzag (n := n) a) (y + a) (2 * (-y).val + 1) := by
  rw [occursAt_iff_getElem?]
  unfold projectionZigzag
  simpa [neg_neg] using flatMap_pair_snd_getElem? a (-y)

private lemma occurs_ordered {n : ℕ} [NeZero n] (a q : ZMod n)
    (e o : ℕ)
    (hE : OccursAt (projectionZigzag (n := n) a) q e)
    (hO : OccursAt (projectionZigzag (n := n) a) q o)
    (hne : e ≠ o) :
    ∃ i j, i = min e o ∧ j = max e o ∧ i < j ∧
      OccursAt (projectionZigzag (n := n) a) q i ∧
      OccursAt (projectionZigzag (n := n) a) q j := by
  refine ⟨min e o, max e o, rfl, rfl, ?_, ?_, ?_⟩
  · by_cases h : e < o
    · rw [Nat.min_eq_left (le_of_lt h), Nat.max_eq_right (le_of_lt h)]
      exact h
    · have ho : o < e := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      rw [Nat.min_eq_right (le_of_lt ho), Nat.max_eq_left (le_of_lt ho)]
      exact ho
  · by_cases h : e < o
    · simpa [Nat.min_eq_left (le_of_lt h)] using hE
    · have ho : o < e := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      simpa [Nat.min_eq_right (le_of_lt ho)] using hO
  · by_cases h : e < o
    · simpa [Nat.max_eq_right (le_of_lt h)] using hO
    · have ho : o < e := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
      simpa [Nat.max_eq_left (le_of_lt ho)] using hE

private lemma cross_swap_last {a b c d : ℕ} (hab : a < b) :
    Cross a b c d ↔ Cross a b d c := by
  have h := chordCross_swap_right a b c d
  simpa [ChordCross, Nat.min_eq_left (le_of_lt hab), Nat.max_eq_right (le_of_lt hab)] using h

private lemma cross_ordered_snd {a b c d : ℕ} (hab : a < b) :
    Cross a b c d ↔ Cross a b (min c d) (max c d) := by
  by_cases hcd : c < d
  · simpa [Nat.min_eq_left (le_of_lt hcd), Nat.max_eq_right (le_of_lt hcd)]
  · have hdc : d ≤ c := le_of_not_gt hcd
    by_cases hEq : c = d
    · subst c
      simp
    · have hdc' : d < c := lt_of_le_of_ne hdc (Ne.symm hEq)
      rw [cross_swap_last hab]
      simp [Nat.min_eq_right (le_of_lt hdc'), Nat.max_eq_left (le_of_lt hdc')]

/-- The `ZMod n` zigzag gives a common noncrossing order of the
multiplicative group `Multiplicative (ZMod n)`. -/
theorem multiplicativeZMod_hasCommonNoncrossingOrder (n : ℕ) [NeZero n] :
    HasCommonNoncrossingOrder (Multiplicative (ZMod n)) := by
  let p : Point (Multiplicative (ZMod n)) → ℕ := fun pt =>
    match pt with
    | Sum.inl x => 2 * (Multiplicative.toAdd x).val
    | Sum.inr x => 2 * (-(Multiplicative.toAdd x)).val + 1
  refine ⟨p, ?_, ?_⟩
  · intro x y hxy
    cases x with
    | inl xi =>
        cases y with
        | inl yi =>
            simp [p] at hxy
            have hval : (Multiplicative.toAdd xi).val = (Multiplicative.toAdd yi).val := by
              omega
            have heq : Multiplicative.toAdd xi = Multiplicative.toAdd yi :=
              ZMod.val_injective n hval
            simpa using congrArg Multiplicative.ofAdd heq
        | inr yi =>
            simp [p] at hxy
            omega
    | inr xi =>
        cases y with
        | inl yi =>
            simp [p] at hxy
            omega
        | inr yi =>
            simp [p] at hxy
            have hval : (-(Multiplicative.toAdd xi)).val = (-(Multiplicative.toAdd yi)).val := by
              omega
            have hneg : -(Multiplicative.toAdd xi) = -(Multiplicative.toAdd yi) :=
              ZMod.val_injective n hval
            have heq : Multiplicative.toAdd xi = Multiplicative.toAdd yi := neg_injective hneg
            simpa using congrArg Multiplicative.ofAdd heq
  · intro g x y hxy
    let a : ZMod n := -(Multiplicative.toAdd g)
    let qx : ZMod n := Multiplicative.toAdd x
    let qy : ZMod n := Multiplicative.toAdd y
    let ex : ℕ := 2 * qx.val
    let ox : ℕ := 2 * (-(qx + Multiplicative.toAdd g)).val + 1
    let ey : ℕ := 2 * qy.val
    let oy : ℕ := 2 * (-(qy + Multiplicative.toAdd g)).val + 1
    have hxE : OccursAt (projectionZigzag (n := n) a) qx ex := by
      simpa [ex, qx] using projectionZigzag_occurs_E a qx
    have hxO : OccursAt (projectionZigzag (n := n) a) qx ox := by
      have h := projectionZigzag_occurs_O a (qx + Multiplicative.toAdd g)
      simpa [a, ox] using h
    have hyE : OccursAt (projectionZigzag (n := n) a) qy ey := by
      simpa [ey, qy] using projectionZigzag_occurs_E a qy
    have hyO : OccursAt (projectionZigzag (n := n) a) qy oy := by
      have h := projectionZigzag_occurs_O a (qy + Multiplicative.toAdd g)
      simpa [a, oy] using h
    have hex_ne_ox : ex ≠ ox := by
      dsimp [ex, ox]
      omega
    have hey_ne_oy : ey ≠ oy := by
      dsimp [ey, oy]
      omega
    have hxq : qx ≠ qy := by
      intro h
      have hx : x = y := by
        simpa using congrArg Multiplicative.ofAdd h
      exact hxy hx
    rcases occurs_ordered a qx ex ox hxE hxO hex_ne_ox with
      ⟨ix, jx, hix, hjx, hx_lt, hx_ix, hx_jx⟩
    rcases occurs_ordered a qy ey oy hyE hyO hey_ne_oy with
      ⟨iy, jy, hiy, hjy, hy_lt, hy_iy, hy_jy⟩
    have hpair : ¬ Cross ix jx iy jy :=
      NestedWord.equalPairs_noncrossing (projectionZigzag_nested (n := n) a)
        (fun q => Or.inr (projectionZigzag_count_eq_two (n := n) a q))
        qx qy ix jx iy jy hxq hx_lt hy_lt hx_ix hx_jx hy_iy hy_jy
    intro hcross
    have hcross' : ChordCross ex ox ey oy := by
      simpa [p, E, O, ex, ox, ey, oy, qx, qy, toAdd_mul] using hcross
    have hc1 : ChordCross ex ox oy ey := (chordCross_swap_right ex ox ey oy).1 hcross'
    have hc2 : Cross ix jx oy ey := by
      simpa [ChordCross, ex, ox, hix, hjx] using hc1
    have hc3 : Cross ix jx iy jy := by
      simpa [hiy, hjy, Nat.min_comm, Nat.max_comm] using
        ((cross_ordered_snd hx_lt).1 hc2)
    exact hpair hc3

private lemma hasCommonNoncrossingOrder_transport
    {G H : Type*}
    [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H]
    (e : G ≃* H) (h : HasCommonNoncrossingOrder H) :
    HasCommonNoncrossingOrder G := by
  rcases h with ⟨p, hp, hnc⟩
  let q : Point G → ℕ := fun pt =>
    match pt with
    | Sum.inl x => p (Sum.inl (e x))
    | Sum.inr x => p (Sum.inr (e x))
  refine ⟨q, ?_, ?_⟩
  · intro a b hq
    cases a with
    | inl a' =>
        cases b with
        | inl b' =>
            simp [q] at hq
            have hpoint : Sum.inl (e a') = Sum.inl (e b') := hp hq
            have hsum : e a' = e b' := Sum.inl.inj hpoint
            have h : a' = b' := e.injective hsum
            exact congrArg Sum.inl h
        | inr b' =>
            simp [q] at hq
            have hpoint : Sum.inl (e a') = Sum.inr (e b') := hp hq
            exact (nomatch hpoint)
    | inr a' =>
        cases b with
        | inl b' =>
            simp [q] at hq
            have hpoint : Sum.inr (e a') = Sum.inl (e b') := hp hq
            exact (nomatch hpoint)
        | inr b' =>
            simp [q] at hq
            have hpoint : Sum.inr (e a') = Sum.inr (e b') := hp hq
            have hsum : e a' = e b' := Sum.inr.inj hpoint
            have h : a' = b' := e.injective hsum
            exact congrArg Sum.inr h
  · intro g x y hxy
    have hx' : e x ≠ e y := by
      intro h
      exact hxy (e.injective h)
    have hnc' := hnc (e g) (e x) (e y) hx'
    simpa [q, E, O, map_mul] using hnc'

/-- A common noncrossing order is transported along a group isomorphism. -/
theorem hasCommonNoncrossingOrder_congr
    {G H : Type*}
    [Group G] [Fintype G] [DecidableEq G]
    [Group H] [Fintype H] [DecidableEq H]
    (e : G ≃* H) :
    HasCommonNoncrossingOrder G ↔ HasCommonNoncrossingOrder H := by
  constructor
  · intro h
    exact hasCommonNoncrossingOrder_transport (e := e.symm) h
  · intro h
    exact hasCommonNoncrossingOrder_transport (e := e) h

/-- Every finite cyclic group admits a common noncrossing order. -/
theorem isCyclic_implies_commonNoncrossingOrder (G : Type*)
    [Group G] [Fintype G] [DecidableEq G] (h : IsCyclic G) :
    HasCommonNoncrossingOrder G := by
  have hcard : 0 < Nat.card G := Nat.card_pos
  haveI : NeZero (Nat.card G) := ⟨Nat.ne_of_gt hcard⟩
  have hz := multiplicativeZMod_hasCommonNoncrossingOrder (n := Nat.card G)
  exact (hasCommonNoncrossingOrder_congr (G := Multiplicative (ZMod (Nat.card G))) (H := G)
    (zmodCyclicMulEquiv h)).1 hz

/-- A finite group has a common noncrossing order iff it is cyclic. -/
theorem hasCommonNoncrossingOrder_iff_isCyclic
    (G : Type*) [Group G] [Fintype G] [DecidableEq G] :
    HasCommonNoncrossingOrder G ↔ IsCyclic G := by
  constructor
  · exact commonNoncrossingOrder_implies_isCyclic G
  · exact isCyclic_implies_commonNoncrossingOrder G

end FourXOR
end Research
end QIT

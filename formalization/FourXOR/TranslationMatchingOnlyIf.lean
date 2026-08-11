/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.Definitions

/-!
# Only-if direction for translation matchings

A common non-crossing order of the right-translation matchings
`E_x — O_{xg}` forces the group to be cyclic.  This file develops the
combinatorial core: the star equivalence, the sets `S(o)`, and the
increasing sequence of `O`-points.
-/

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*} [Group G]

/-- A point of the matching diagram: an `E`-point or an `O`-point. -/
abbrev Point (G : Type*) := G ⊕ G

/-- The `E`-point of `x`. -/
def E (x : G) : Point G := Sum.inl x

/-- The `O`-point of `x`. -/
def O (x : G) : Point G := Sum.inr x

/-- Two chords with endpoint positions `(a,b)` and `(c,d)` cross. -/
def Cross (a b c d : ℕ) : Prop :=
  (a < c ∧ c < b ∧ b < d) ∨ (a < d ∧ d < b ∧ b < c) ∨
    (c < a ∧ a < d ∧ d < b) ∨ (d < a ∧ a < c ∧ c < b)

/-- The star equivalence: for `x ≠ 1`, `E_x` and `O_{xg}` lie on the same
side of `O_g`. -/
lemma same_side (p : Point G → ℕ) (hp : Function.Injective p) {x g : G}
    (hfirst : p (E 1) = 0)
    (hnc : ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    (hx : x ≠ 1) :
    p (E x) < p (O g) ↔ p (O (x * g)) < p (O g) := by
  have hEc : p (E 1) < p (E x) := by
    have hne : p (E x) ≠ p (E 1) := by
      intro h
      exact hx (Sum.inl.inj (hp h))
    omega
  have h0d : p (E 1) < p (O (x * g)) := by
    have hne : p (O (x * g)) ≠ p (E 1) := by
      intro h
      exact (nomatch (hp h))
    omega
  have hOd : p (O (x * g)) ≠ p (O g) := by
    intro h
    have hEq : Sum.inr (x * g) = Sum.inr g := hp h
    have hEq' : x * g = g := Sum.inr.inj hEq
    have hxg : x * g = (1 : G) * g := by simpa using hEq'
    exact hx (mul_right_cancel hxg)
  have hEc_ne : p (E x) ≠ p (O g) := by
    intro h
    exact (nomatch (hp h))
  constructor
  · intro hcb
    by_contra hdb
    have hbd : p (O g) < p (O (x * g)) := by omega
    exact hnc (Or.inl ⟨hEc, hcb, hbd⟩)
  · intro hdb
    by_contra hcb
    have hbc : p (O g) < p (E x) := by omega
    exact hnc (Or.inr (Or.inl ⟨h0d, hdb, hbc⟩))

end FourXOR
end Research
end QIT

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- The set of `E`-points before `O_o`. -/
def S (p : Point G → ℕ) (o : G) : Finset G :=
  Finset.univ.filter (fun x => p (E x) < p (O o))

/-- The star characterization of `S(o)`. -/
lemma S_eq (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    (o : G) :
    S p o = insert 1 (Finset.univ.filter (fun x => x ≠ 1 ∧ p (O (x * o)) < p (O o))) := by
  ext x
  by_cases hx : x = 1
  · subst x
    simp [S]
    have h0 : p (E 1) < p (O o) := by
      have hne : p (O o) ≠ p (E 1) := by
        intro h
        exact (nomatch (hp h))
      omega
    exact h0
  · simp [S, hx]
    exact same_side p hp hfirst (hnc o x hx) hx

/-- The `O`-points in increasing order of position. -/
def os (p : Point G → ℕ) (hp : Function.Injective p) : List G := by
  letI : IsTrans G (fun a b : G => p (O a) ≤ p (O b)) :=
    ⟨fun _ _ _ h1 h2 => le_trans h1 h2⟩
  letI : Std.Antisymm (fun a b : G => p (O a) ≤ p (O b)) :=
    ⟨fun a b h1 h2 => Sum.inr.inj (hp (le_antisymm h1 h2))⟩
  letI : Std.Total (fun a b : G => p (O a) ≤ p (O b)) :=
    ⟨fun a b => le_total (p (O a)) (p (O b))⟩
  exact Finset.univ.sort (fun a b => p (O a) ≤ p (O b))

/-- The sorted `O`-point list contains every group element. -/
lemma os_mem (p : Point G → ℕ) (hp : Function.Injective p) (x : G) : x ∈ os p hp := by
  simp [os]

/-- The sorted `O`-point list has no duplicates. -/
lemma os_nodup (p : Point G → ℕ) (hp : Function.Injective p) : (os p hp).Nodup := by
  simp [os]

/-- The `O`-point list has length `|G|`. -/
lemma os_length (p : Point G → ℕ) (hp : Function.Injective p) :
    (os p hp).length = Fintype.card G := by
  simp [os]

/-- The `O`-point list is increasing by position. -/
lemma os_pairwise (p : Point G → ℕ) (hp : Function.Injective p) :
    List.Pairwise (fun a b => p (O a) ≤ p (O b)) (os p hp) := by
  simp [os]

/-- The `O`-points are strictly increasing by position in the sorted list. -/
lemma os_strict (p : Point G → ℕ) (hp : Function.Injective p) :
    List.Pairwise (fun a b => p (O a) < p (O b)) (os p hp) := by
  rw [List.pairwise_iff_get]
  intro i j hij
  have hle : p (O ((os p hp).get i)) ≤ p (O ((os p hp).get j)) :=
    List.Pairwise.rel_get_of_lt (os_pairwise p hp) hij
  have hne : p (O ((os p hp).get i)) ≠ p (O ((os p hp).get j)) := by
    intro h
    have hpair : O ((os p hp).get i) = O ((os p hp).get j) := hp h
    have hget : (os p hp).get i = (os p hp).get j := Sum.inr.inj hpair
    have hinj : Function.Injective (os p hp).get :=
      (List.nodup_iff_injective_get).1 (os_nodup p hp)
    have hEq : i = j := hinj hget
    exact (Nat.lt_irrefl i.1) (by simpa [hEq] using (show i.1 < j.1 from hij))
  exact lt_of_le_of_ne hle hne

/-- In the sorted `O`-list, position comparison is index comparison. -/
lemma os_index_lt (p : Point G → ℕ) (hp : Function.Injective p)
    {i j : ℕ} (hi : i < (os p hp).length) (hj : j < (os p hp).length) :
    p (O ((os p hp).get ⟨i, hi⟩)) < p (O ((os p hp).get ⟨j, hj⟩)) ↔ i < j := by
  constructor
  · intro h
    by_contra hnot
    have hle : j ≤ i := Nat.le_of_not_gt hnot
    by_cases hEq : i = j
    · subst j
      exact (lt_irrefl _ h)
    · have hji : j < i := lt_of_le_of_ne hle (Ne.symm hEq)
      have h' : p (O ((os p hp).get ⟨j, hj⟩)) < p (O ((os p hp).get ⟨i, hi⟩)) :=
        List.Pairwise.rel_get_of_lt (os_strict p hp)
          (show (⟨j, hj⟩ : Fin (os p hp).length) < ⟨i, hi⟩ from hji)
      omega
  · intro hij
    exact List.Pairwise.rel_get_of_lt (os_strict p hp)
      (show (⟨i, hi⟩ : Fin (os p hp).length) < ⟨j, hj⟩ from hij)

/-- The `k`-th `O`-point lies in the first `j` positions when `k < j`. -/
lemma os_get_mem_take (p : Point G → ℕ) (hp : Function.Injective p)
    {k j : ℕ} (hk : k < (os p hp).length) (hkj : k < j) :
    (os p hp).get ⟨k, hk⟩ ∈ (os p hp).take j := by
  have hkTake : k < ((os p hp).take j).length := by
    rw [List.length_take]
    omega
  simpa [List.getElem_take] using (List.getElem_mem hkTake)

/-- Membership in the first `j` positions gives an index `< j`. -/
lemma os_mem_take_index (p : Point G → ℕ) (hp : Function.Injective p)
    {y : G} {j : ℕ} (hy : y ∈ (os p hp).take j) :
    ∃ k, k < j ∧ ∃ hk : k < (os p hp).length, (os p hp)[k]'hk = y := by
  rcases List.getElem_of_mem hy with ⟨k, hkTake, hget⟩
  have hk : k < (os p hp).length := by
    have hle : ((os p hp).take j).length ≤ (os p hp).length := by
      rw [List.length_take]
      omega
    omega
  refine ⟨k, ?_, ?_⟩
  · have hmin : k < min j (os p hp).length := by
      simpa [List.length_take] using hkTake
    omega
  · refine ⟨hk, ?_⟩
    have hgetTake : ((os p hp).take j)[k] = (os p hp)[k]'hk :=
      List.getElem_take (xs := os p hp) (j := j) (i := k) (h := hkTake)
    rw [← hgetTake]
    exact hget

/-- Taking a prefix of a duplicate-free list keeps it duplicate-free. -/
lemma nodup_take {α : Type*} {l : List α} (h : l.Nodup) (n : ℕ) :
    (l.take n).Nodup := by
  rw [List.nodup_iff_injective_get]
  intro i j hij
  have hi : i.1 < l.length := by
    have hi' : i.1 < min n l.length := by
      simpa [List.length_take] using i.2
    omega
  have hj : j.1 < l.length := by
    have hj' : j.1 < min n l.length := by
      simpa [List.length_take] using j.2
    omega
  have hti : (l.take n)[i.1]'i.2 = l[i.1]'hi :=
    List.getElem_take (xs := l) (j := n) (i := i.1) (h := i.2)
  have htj : (l.take n)[j.1]'j.2 = l[j.1]'hj :=
    List.getElem_take (xs := l) (j := n) (i := j.1) (h := j.2)
  have hEq : l.get ⟨i.1, hi⟩ = l.get ⟨j.1, hj⟩ := by
    calc
      l.get ⟨i.1, hi⟩ = (l.take n).get i := hti.symm
      _ = (l.take n).get j := hij
      _ = l.get ⟨j.1, hj⟩ := htj
  have hFin : (⟨i.1, hi⟩ : Fin l.length) = ⟨j.1, hj⟩ :=
    (List.nodup_iff_injective_get).1 h hEq
  exact Fin.eq_of_val_eq (congrArg (fun a : Fin l.length => a.1) hFin)

/-- Prefixes of a list are nested. -/
lemma take_subset_take {α : Type*} {l : List α} {m n : ℕ} (hmn : m ≤ n)
    {a : α} (ha : a ∈ l.take m) : a ∈ l.take n :=
  List.Sublist.mem ha (List.take_sublist_take_left hmn)

/-- The set `S(o_j)` consists of `1` together with `{y o_j⁻¹ | y before o_j}`. -/
lemma S_take (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    {j : ℕ} (hj : j < (os p hp).length) :
    S p ((os p hp).get ⟨j, hj⟩) =
      insert 1 (((os p hp).take j).toFinset.image
        (fun y => y * ((os p hp).get ⟨j, hj⟩)⁻¹)) := by
  ext x
  by_cases hx : x = 1
  · subst x
    simp [S]
    have h0 : p (E 1) < p (O ((os p hp).get ⟨j, hj⟩)) := by
      have hne : p (O ((os p hp).get ⟨j, hj⟩)) ≠ p (E 1) := by
        intro h
        exact (nomatch (hp h))
      omega
    exact h0
  · have hstar : p (E x) < p (O ((os p hp).get ⟨j, hj⟩)) ↔
        p (O (x * (os p hp).get ⟨j, hj⟩)) <
          p (O ((os p hp).get ⟨j, hj⟩)) :=
      same_side p hp hfirst (hnc ((os p hp).get ⟨j, hj⟩) x hx) hx
    rw [S]
    simp [hx]
    constructor
    · intro hE
      have hz : p (O (x * (os p hp).get ⟨j, hj⟩)) <
          p (O ((os p hp).get ⟨j, hj⟩)) := hstar.1 hE
      rcases List.getElem_of_mem (os_mem p hp (x * (os p hp).get ⟨j, hj⟩))
        with ⟨k, hk, hget⟩
      have hklt : k < j := by
        have hlt : p (O ((os p hp).get ⟨k, hk⟩)) <
            p (O ((os p hp).get ⟨j, hj⟩)) := by
          rw [← hget] at hz
          exact hz
        exact (os_index_lt p hp hk hj).1 hlt
      simpa [hget] using os_get_mem_take p hp hk hklt
    · intro hzmem
      rcases os_mem_take_index p hp hzmem with ⟨k, hklt, hk, hget⟩
      have hz : p (O (x * (os p hp).get ⟨j, hj⟩)) <
          p (O ((os p hp).get ⟨j, hj⟩)) := by
        have hlt : p (O ((os p hp).get ⟨k, hk⟩)) <
            p (O ((os p hp).get ⟨j, hj⟩)) :=
          (os_index_lt p hp hk hj).2 hklt
        simpa [← hget] using hlt
      exact hstar.2 hz

/-- `1` is not among the shifted prefix elements defining `S(o_j)\{1}`. -/
lemma S_take_one_not_mem (p : Point G → ℕ) (hp : Function.Injective p)
    {j : ℕ} (hj : j < (os p hp).length) :
    (1 : G) ∉ ((os p hp).take j).toFinset.image
      (fun y => y * ((os p hp).get ⟨j, hj⟩)⁻¹) := by
  intro hmem
  rw [Finset.mem_image] at hmem
  rcases hmem with ⟨y, hy, hy_eq⟩
  have hyo : y = (os p hp).get ⟨j, hj⟩ := (mul_inv_eq_one).1 hy_eq
  have hyList : y ∈ (os p hp).take j := (List.mem_toFinset).1 hy
  rcases os_mem_take_index p hp hyList with ⟨k, hklt, hk, hget⟩
  have hget' : (os p hp).get ⟨k, hk⟩ = (os p hp).get ⟨j, hj⟩ := by
    simpa [hyo, hget]
  have hFin : (⟨k, hk⟩ : Fin (os p hp).length) = ⟨j, hj⟩ :=
    (List.nodup_iff_injective_get).1 (os_nodup p hp) hget'
  have hEq : k = j := congrArg Fin.val hFin
  exact (Nat.lt_irrefl j) (by simpa [hEq] using hklt)

/-- The cardinality of `S(o_j)` is `j + 1`. -/
lemma S_card (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    {j : ℕ} (hj : j < (os p hp).length) :
    (S p ((os p hp).get ⟨j, hj⟩)).card = j + 1 := by
  rw [S_take p hp hfirst hnc hj]
  have hnotmem : (1 : G) ∉ ((os p hp).take j).toFinset.image
      (fun y => y * ((os p hp).get ⟨j, hj⟩)⁻¹) :=
    S_take_one_not_mem p hp hj
  have hcardIm : (((os p hp).take j).toFinset.image
      (fun y => y * ((os p hp).get ⟨j, hj⟩)⁻¹)).card = j := by
    rw [Finset.card_image_of_injective]
    · rw [List.toFinset_card_of_nodup (nodup_take (os_nodup p hp) j)]
      rw [List.length_take]
      have hmin : min j (os p hp).length = j := by omega
      simp [hmin]
    · intro a b h
      exact mul_right_cancel h
  rw [Finset.card_insert_of_notMem hnotmem, hcardIm]

/-- The sets `S(o_j)` are increasing with `j`. -/
lemma S_subset (p : Point G → ℕ) (hp : Function.Injective p)
    {j : ℕ} (hprev : j < (os p hp).length) (hj : j + 1 < (os p hp).length) :
    S p ((os p hp).get ⟨j, hprev⟩) ⊆ S p ((os p hp).get ⟨j + 1, hj⟩) := by
  intro x hx
  have hx' : x ∈ Finset.univ ∧
      p (E x) < p (O ((os p hp).get ⟨j, hprev⟩)) := by
    simpa [S] using hx
  have hlt : p (O ((os p hp).get ⟨j, hprev⟩)) <
      p (O ((os p hp).get ⟨j + 1, hj⟩)) :=
    (os_index_lt p hp hprev (by omega)).2 (Nat.lt_succ_self j)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, lt_trans hx'.2 hlt⟩

/-- Recursion for the `S`-sets: `S(o_{j+1}) = {1} ∪ ((S(o_j)\{1})·d_j) ∪ {d_j}`
with `d_j = o_j o_{j+1}^{-1}`. -/
lemma S_succ (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    {j : ℕ} (hprev : j < (os p hp).length) (hj : j + 1 < (os p hp).length) :
    S p ((os p hp).get ⟨j + 1, hj⟩) =
      insert 1 (((S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
        (fun x => x * (((os p hp).get ⟨j, hprev⟩) * ((os p hp).get ⟨j + 1, hj⟩)⁻¹)))
        ∪ {(((os p hp).get ⟨j, hprev⟩) * ((os p hp).get ⟨j + 1, hj⟩)⁻¹)}) := by
  set o : G := (os p hp).get ⟨j, hprev⟩
  set o' : G := (os p hp).get ⟨j + 1, hj⟩
  set d : G := o * (o'⁻¹)
  ext x
  by_cases hx : x = 1
  · subst x
    have h0 : p (E 1) < p (O o') := by
      have hne : p (O o') ≠ p (E 1) := by
        intro h
        exact (nomatch (hp h))
      omega
    simp [S, h0]
  · have hstar : p (E x) < p (O o') ↔ p (O (x * o')) < p (O o') :=
      same_side p hp hfirst (hnc o' x hx) hx
    rw [S_take p hp hfirst hnc hprev]
    rw [S]
    have hnotmem : (1 : G) ∉ ((os p hp).take j).toFinset.image
        (fun y => y * o⁻¹) := by
      simpa [o] using S_take_one_not_mem p hp hprev
    rw [Finset.sdiff_singleton_eq_erase, Finset.erase_insert hnotmem]
    dsimp [d]
    simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton,
      hx, false_or]
    constructor
    · intro hE
      have hE' : p (E x) < p (O o') := (Finset.mem_filter.mp hE).2
      have hz : p (O (x * o')) < p (O o') := hstar.1 hE'
      rcases List.getElem_of_mem (os_mem p hp (x * o')) with ⟨k, hk, hget⟩
      have hklt' : k < j + 1 := by
        have hlt : p (O ((os p hp).get ⟨k, hk⟩)) < p (O o') := by
          rw [← hget] at hz
          exact hz
        exact (os_index_lt p hp hk (by omega)).1 hlt
      by_cases hkj : k = j
      · have hfin : (⟨k, hk⟩ : Fin (os p hp).length) = ⟨j, hprev⟩ := Fin.ext hkj
        have hgetj0 : (os p hp).get ⟨k, hk⟩ = (os p hp).get ⟨j, hprev⟩ :=
          congrArg (fun i : Fin (os p hp).length => (os p hp).get i) hfin
        have hgetj : (os p hp).get ⟨j, hprev⟩ = x * o' := by
          rw [← hgetj0]
          exact hget
        have hgetj1 : o = x * o' := by
          simpa [o] using hgetj
        have hxd : x = o * o'⁻¹ := by
          calc
            x = (x * o') * o'⁻¹ := by group
            _ = o * o'⁻¹ := by rw [← hgetj1]
        right
        exact hxd
      · have hklt : k < j := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hklt') hkj
        have hy : (os p hp).get ⟨k, hk⟩ ∈ (os p hp).take j :=
          os_get_mem_take p hp hk hklt
        have hz1 : (os p hp).get ⟨k, hk⟩ = x * o' := by
          simpa [hget]
        have hx1 : x = (os p hp).get ⟨k, hk⟩ * o'⁻¹ := by
          calc
            x = (x * o') * o'⁻¹ := by group
            _ = (os p hp).get ⟨k, hk⟩ * o'⁻¹ := by rw [← hz1]
        have hxeq : x = ((os p hp).get ⟨k, hk⟩ * o⁻¹) * (o * o'⁻¹) := by
          calc
            x = (os p hp).get ⟨k, hk⟩ * o'⁻¹ := hx1
            _ = ((os p hp).get ⟨k, hk⟩ * o⁻¹) * (o * o'⁻¹) := by group
        left
        rw [Finset.mem_image]
        refine ⟨(os p hp).get ⟨k, hk⟩ * o⁻¹, ?_, ?_⟩
        · rw [Finset.mem_image]
          exact ⟨(os p hp).get ⟨k, hk⟩, List.mem_toFinset.2 hy, rfl⟩
        · exact hxeq.symm
    · intro hmem
      rcases hmem with hleft | hright
      · rcases (Finset.mem_image.mp hleft) with ⟨z, hzmem, hzeq⟩
        rcases (Finset.mem_image.mp hzmem) with ⟨t, htmem, hteq⟩
        have hxeq : x = t * o'⁻¹ := by
          calc
            x = z * (o * o'⁻¹) := hzeq.symm
            _ = (t * o⁻¹) * (o * o'⁻¹) := by rw [hteq]
            _ = t * o'⁻¹ := by group
        have htlist : t ∈ (os p hp).take j := List.mem_toFinset.1 htmem
        rcases os_mem_take_index p hp htlist with ⟨k, hklt, hk, hget⟩
        have hz' : p (O (x * o')) < p (O o') := by
          have hxeq' : x * o' = t := by
            calc
              x * o' = (t * o'⁻¹) * o' := by rw [hxeq]
              _ = t := by group
          have hlt : p (O ((os p hp).get ⟨k, hk⟩)) < p (O o') :=
            (os_index_lt p hp hk (by omega)).2 (by omega)
          rw [hxeq']
          simpa [← hget] using hlt
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hstar.2 hz'⟩
      · have hx' : x * o' = o := by
          rw [hright]
          group
        have hz' : p (O (x * o')) < p (O o') := by
          rw [hx']
          exact (os_index_lt p hp hprev (by omega)).2 (Nat.lt_succ_self j)
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hstar.2 hz'⟩

/-- `{1, d, ..., d^{j-1}}` as a finset. -/
def powSet (d : G) (j : ℕ) : Finset G :=
  (Finset.range j).image (fun i : ℕ => d ^ i)

@[simp] lemma powSet_zero (d : G) : powSet d 0 = ∅ := by
  simp [powSet]

@[simp] lemma powSet_one (d : G) : powSet d 1 = {1} := by
  simp [powSet]

@[simp] lemma powSet_two (d : G) : powSet d 2 = ({1, d} : Finset G) := by
  ext x
  simp only [powSet, Finset.mem_image, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · rintro ⟨a, ha, rfl⟩
    interval_cases a <;> simp
  · intro hx
    rcases hx with hx1 | hxd
    · exact ⟨0, by norm_num, by simpa [hx1]⟩
    · exact ⟨1, by norm_num, by simpa [hxd]⟩

lemma one_mem_powSet (d : G) {j : ℕ} (hj : 0 < j) : (1 : G) ∈ powSet d j := by
  rw [powSet]
  exact Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hj, by simp⟩

lemma pow_mem_powSet (d : G) {i j : ℕ} (hij : i < j) : d ^ i ∈ powSet d j := by
  rw [powSet]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, rfl⟩

lemma powSet_mem (d : G) {j : ℕ} {z : G} (hz : z ∈ powSet d j) :
    ∃ i, i < j ∧ d ^ i = z := by
  rw [powSet] at hz
  rcases Finset.mem_image.mp hz with ⟨i, hi, hi_eq⟩
  exact ⟨i, Finset.mem_range.mp hi, hi_eq⟩

lemma powSet_card_le (d : G) (j : ℕ) : (powSet d j).card ≤ j := by
  rw [powSet]
  simpa using
    (Finset.card_image_le : ((Finset.range j).image (fun i : ℕ => d ^ i)).card ≤
      (Finset.range j).card)

lemma powSet_injOn (d : G) {j : ℕ} (hcard : (powSet d (j + 1)).card = j + 1) :
    Set.InjOn (fun i : ℕ => d ^ i) (↑(Finset.range (j + 1))) := by
  have hcard' : ((Finset.range (j + 1)).image (fun i : ℕ => d ^ i)).card =
      (Finset.range (j + 1)).card := by
    simpa [powSet, Finset.card_range] using hcard
  exact (Finset.card_image_iff.mp hcard')

lemma pow_inj_of_card (d : G) {j : ℕ} (hcard : (powSet d (j + 1)).card = j + 1)
    {i k : ℕ} (hi : i < j + 1) (hk : k < j + 1) (h : d ^ i = d ^ k) : i = k := by
  exact powSet_injOn d hcard (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hk) h

/-- `1` is in every `S(o_j)`. -/
lemma S_mem_one (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    {j : ℕ} (hj : j < (os p hp).length) :
    (1 : G) ∈ S p ((os p hp).get ⟨j, hj⟩) := by
  rw [S_take p hp hfirst hnc hj]
  simp

/-- If `1` lies in the recursive right-hand side, its cardinality is bounded
by `j + 1`. -/
lemma card_rec_rhs_le_of_one_mem (S : Finset G) (d_j : G) {j : ℕ}
    (h1S : (1 : G) ∈ S)
    (hone : (1 : G) ∈ (S \ {1}).image (fun x => x * d_j) ∪ {d_j})
    (hcardS : S.card = j + 1) :
    (insert 1 (((S \ {1}).image (fun x => x * d_j)) ∪ {d_j})).card ≤ j + 1 := by
  rw [Finset.insert_eq_of_mem hone]
  have hle : (((S \ {1}).image (fun x => x * d_j)) ∪ {d_j}).card ≤
      ((S \ {1}).image (fun x => x * d_j)).card + 1 :=
    Finset.card_union_le _ _
  have hcardIm : ((S \ {1}).image (fun x => x * d_j)).card = (S \ {1}).card :=
    Finset.card_image_of_injective _ (fun a b h => mul_right_cancel h)
  have hcardErase : (S \ {1}).card = j := by
    rw [Finset.sdiff_singleton_eq_erase]
    rw [Finset.card_erase_of_mem h1S]
    omega
  omega

/-- The recursive right-hand side has cardinality `j + 2`, so `1` cannot
already lie in the shifted image union. -/
lemma rec_no_overlap (S : Finset G) (d_j : G) {j : ℕ}
    (h1S : (1 : G) ∈ S) (hcardS : S.card = j + 1)
    (hT : (insert 1 (((S \ {1}).image (fun x => x * d_j)) ∪ {d_j})).card = j + 2) :
    (1 : G) ∉ (S \ {1}).image (fun x => x * d_j) ∪ {d_j} := by
  intro hone
  have hle := card_rec_rhs_le_of_one_mem S d_j h1S hone hcardS
  omega

/-- The step `d_j` cannot be the identity. -/
lemma rec_dj_ne_one (S : Finset G) (d_j : G) {j : ℕ}
    (h1S : (1 : G) ∈ S) (hcardS : S.card = j + 1)
    (hT : (insert 1 (((S \ {1}).image (fun x => x * d_j)) ∪ {d_j})).card = j + 2) :
    d_j ≠ 1 := by
  intro hdj
  have hone : (1 : G) ∈ (S \ {1}).image (fun x => x * d_j) ∪ {d_j} := by
    rw [Finset.mem_union]
    right
    simp [hdj]
  exact rec_no_overlap S d_j h1S hcardS hT hone

/-- Equal indices give equal `O`-points (up to proof irrelevance). -/
lemma os_get_eq_of_val_eq (p : Point G → ℕ) (hp : Function.Injective p)
    {i j : ℕ} (hi : i < (os p hp).length) (hj : j < (os p hp).length)
    (h : i = j) : (os p hp).get ⟨i, hi⟩ = (os p hp).get ⟨j, hj⟩ := by
  have hfin : (⟨i, hi⟩ : Fin (os p hp).length) = ⟨j, hj⟩ := Fin.ext h
  exact congrArg (fun k : Fin (os p hp).length => (os p hp).get k) hfin

/-- The recursion turns the power set `powSet d (j+1)` into
`powSet d (j+2)`. -/
lemma powSet_succ (d : G) {j : ℕ} (hcard : (powSet d (j + 1)).card = j + 1) :
    insert 1 (((powSet d (j + 1) \ {1}).image (fun x => x * d)) ∪ {d}) =
      powSet d (j + 2) := by
  ext z
  constructor
  · intro hz
    rcases Finset.mem_insert.mp hz with hz1 | hzR
    · rw [hz1]
      simpa using (pow_mem_powSet d (i := 0) (j := j + 2) (by omega))
    · rcases Finset.mem_union.mp hzR with hzIm | hzd
      · rcases Finset.mem_image.mp hzIm with ⟨x, hxmem, hxeq⟩
        have hxS : x ∈ powSet d (j + 1) := (Finset.mem_sdiff.mp hxmem).1
        have hxne : x ≠ 1 := by
          intro hx1
          exact (Finset.mem_sdiff.mp hxmem).2 (by simpa [hx1])
        rcases powSet_mem d hxS with ⟨i, hi, hpow⟩
        have hi0 : i ≠ 0 := by
          intro hi0'
          have hx1 : 1 = x := by simpa [hi0'] using hpow
          exact hxne hx1.symm
        have hz' : z = d ^ (i + 1) := by
          calc
            z = x * d := hxeq.symm
            _ = d ^ i * d := by rw [hpow]
            _ = d ^ (i + 1) := by rw [pow_succ]
        rw [hz']
        exact pow_mem_powSet d (i := i + 1) (j := j + 2) (by omega)
      · rw [Finset.mem_singleton.mp hzd]
        simpa using (pow_mem_powSet d (i := 1) (j := j + 2) (by omega))
  · intro hz
    rcases powSet_mem d hz with ⟨i, hi, hpow⟩
    rw [Finset.mem_insert]
    by_cases hi0 : i = 0
    · left
      simpa [← hpow, hi0]
    · have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
      right
      rw [Finset.mem_union]
      by_cases hi1' : i = 1
      · right
        rw [← hpow]
        simp [hi1']
      · left
        refine Finset.mem_image.mpr ⟨d ^ (i - 1), ?_, ?_⟩
        · refine Finset.mem_sdiff.mpr ?_
          constructor
          · have hi_lt : i - 1 < j + 1 := by omega
            exact pow_mem_powSet d (i := i - 1) (j := j + 1) hi_lt
          · intro h1
            rw [Finset.mem_singleton] at h1
            have hEq : i - 1 = 0 :=
              pow_inj_of_card d hcard (by omega) (by omega) (by simpa using h1)
            omega
        · rw [← hpow]
          have hi_eq : i = (i - 1) + 1 := by omega
          rw [hi_eq, pow_succ]
          congr 1

/-- In the recursion for `S`, the step `d_j = o_j o_{j+1}^{-1}` is constant. -/
lemma S_succ_dj_eq_d (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    {j : ℕ} (hprev : j < (os p hp).length) (hj : j + 1 < (os p hp).length)
    (d : G) (hd_ne : d ≠ 1) (hj1 : 1 ≤ j)
    (hS : S p ((os p hp).get ⟨j, hprev⟩) = powSet d (j + 1)) :
    (os p hp).get ⟨j, hprev⟩ * ((os p hp).get ⟨j + 1, hj⟩)⁻¹ = d := by
  set d_j : G := (os p hp).get ⟨j, hprev⟩ * ((os p hp).get ⟨j + 1, hj⟩)⁻¹
  have hcardS : (S p ((os p hp).get ⟨j, hprev⟩)).card = j + 1 :=
    S_card p hp hfirst hnc hprev
  have hcardT : (S p ((os p hp).get ⟨j + 1, hj⟩)).card = j + 2 := by
    simpa using (S_card p hp hfirst hnc hj)
  have hmem1 : (1 : G) ∈ S p ((os p hp).get ⟨j, hprev⟩) :=
    S_mem_one p hp hfirst hnc hprev
  have hT : (insert 1 (((S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
      (fun x => x * d_j)) ∪ {d_j})).card = j + 2 := by
    change (insert 1 (((S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
      (fun x => x * ((os p hp).get ⟨j, hprev⟩ * ((os p hp).get ⟨j + 1, hj⟩)⁻¹))) ∪
      {((os p hp).get ⟨j, hprev⟩ * ((os p hp).get ⟨j + 1, hj⟩)⁻¹)})).card = j + 2
    rw [← S_succ p hp hfirst hnc hprev hj]
    exact hcardT
  have hno : (1 : G) ∉ (S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
      (fun x => x * d_j) ∪ {d_j} :=
    rec_no_overlap (S p ((os p hp).get ⟨j, hprev⟩)) d_j hmem1 hcardS hT
  have hdjn : d_j ≠ 1 :=
    rec_dj_ne_one (S p ((os p hp).get ⟨j, hprev⟩)) d_j hmem1 hcardS hT
  by_contra hdne
  have hcardPow : (powSet d (j + 1)).card = j + 1 := by
    rw [← hS]
    exact hcardS
  have hd_mem_S : d ∈ S p ((os p hp).get ⟨j, hprev⟩) := by
    rw [hS]
    simpa using (pow_mem_powSet d (i := 1) (j := j + 1) (by omega))
  have hd_mem_T : d ∈ S p ((os p hp).get ⟨j + 1, hj⟩) :=
    S_subset p hp hprev hj hd_mem_S
  have hd_mem_rec : d ∈ insert 1 (((S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
      (fun x => x * d_j)) ∪ {d_j}) := by
    rw [S_succ p hp hfirst hnc hprev hj] at hd_mem_T
    simpa [d_j] using hd_mem_T
  rcases Finset.mem_insert.mp hd_mem_rec with hd1 | hdR
  · exact False.elim (hd_ne hd1)
  · rcases Finset.mem_union.mp hdR with hdim | hddj
    · rcases Finset.mem_image.mp hdim with ⟨x, hxmem, hxeq⟩
      have hxS : x ∈ S p ((os p hp).get ⟨j, hprev⟩) := (Finset.mem_sdiff.mp hxmem).1
      have hxne : x ≠ 1 := by
        intro hx1
        exact (Finset.mem_sdiff.mp hxmem).2 (by simpa [hx1])
      have hxpow' : x ∈ powSet d (j + 1) := by
        rw [← hS]
        exact hxS
      rcases powSet_mem d hxpow' with ⟨i, hi, hpow⟩
      have hi0 : i ≠ 0 := by
        intro hi0'
        have hx1 : 1 = x := by simpa [hi0'] using hpow
        exact hxne hx1.symm
      have hi1 : 1 ≤ i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
      have hxeq' : d ^ i * d_j = d := by
        simpa [hpow] using hxeq
      have hdj0 : d_j = (d ^ i)⁻¹ * d := by
        calc
          d_j = (d ^ i)⁻¹ * (d ^ i * d_j) := by group
          _ = (d ^ i)⁻¹ * d := by rw [hxeq']
      have hdj_z : d_j = d ^ (-(i : ℤ) + 1) := by
        calc
          d_j = (d ^ i)⁻¹ * d := hdj0
          _ = d ^ (-(i : ℤ)) * d ^ (1 : ℤ) := by
            simp [zpow_neg, zpow_natCast]
          _ = d ^ (-(i : ℤ) + 1) := by rw [zpow_add]
      by_cases hi1' : i = 1
      · have hxeq'' : d * d_j = d := by simpa [hi1'] using hxeq'
        have hdj1 : d_j = 1 :=
          mul_left_cancel (a := d) (b := d_j) (c := 1) (by simpa using hxeq'')
        exact hdjn hdj1
      · have hy : d ^ (i - 1) ∈ S p ((os p hp).get ⟨j, hprev⟩) := by
          rw [hS]
          exact pow_mem_powSet d (i := i - 1) (j := j + 1) (by omega)
        have hyne : d ^ (i - 1) ≠ 1 := by
          intro h1
          have hEq : i - 1 = 0 :=
            pow_inj_of_card d hcardPow (by omega) (by omega) (by simpa using h1)
          omega
        have hy_dj : d ^ (i - 1) * d_j = 1 := by
          rw [hdj_z]
          have hzexp : ((i - 1 : ℕ) : ℤ) + (-(i : ℤ) + 1) = 0 := by omega
          rw [← zpow_natCast]
          rw [← zpow_add]
          rw [hzexp]
          simp
        have hone : (1 : G) ∈ (S p ((os p hp).get ⟨j, hprev⟩) \ {1}).image
            (fun x => x * d_j) := by
          exact Finset.mem_image.mpr ⟨d ^ (i - 1),
            Finset.mem_sdiff.mpr ⟨hy, by
              intro h1
              rw [Finset.mem_singleton] at h1
              exact hyne h1⟩, hy_dj⟩
        exact hno (Finset.mem_union.mpr (Or.inl hone))
    · have hddj' : d = d_j := Finset.mem_singleton.mp hddj
      exact hdne hddj'.symm

/-- A common non-crossing order forces the sets `S(o_j)` to be initial
segments of the powers of a single generator. -/
theorem S_pow (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g))))
    (hcard : (os p hp).length = Fintype.card G)
    (hn : 2 ≤ Fintype.card G) :
    ∃ d : G, d ≠ 1 ∧
      ∀ j : ℕ, ∀ hj : j < (os p hp).length,
        S p ((os p hp).get ⟨j, hj⟩) = powSet d (j + 1) := by
  have h0 : 0 < (os p hp).length := by
    rw [hcard]
    omega
  have h1 : 1 < (os p hp).length := by
    rw [hcard]
    omega
  let d : G := (os p hp).get ⟨0, h0⟩ * ((os p hp).get ⟨1, h1⟩)⁻¹
  have hd_ne : d ≠ 1 := by
    intro hd
    have hEq : (os p hp).get ⟨0, h0⟩ = (os p hp).get ⟨1, h1⟩ :=
      (mul_inv_eq_one).1 (by simpa [d] using hd)
    have hFin : (⟨0, h0⟩ : Fin (os p hp).length) = ⟨1, h1⟩ :=
      (List.nodup_iff_injective_get).1 (os_nodup p hp) hEq
    have hEqVal : 0 = 1 := congrArg Fin.val hFin
    omega
  refine ⟨d, hd_ne, ?_⟩
  intro j
  induction j with
  | zero =>
      intro hj
      rw [S_take p hp hfirst hnc hj]
      simp [d, powSet]
  | succ j ih =>
      intro hj'
      have hprev : j < (os p hp).length := by omega
      have hS_j : S p ((os p hp).get ⟨j, hprev⟩) = powSet d (j + 1) := ih hprev
      by_cases hj0 : j = 0
      · subst j
        have hS0 : S p ((os p hp).get ⟨0, hprev⟩) = powSet d 1 := by
          simpa using hS_j
        rw [S_succ p hp hfirst hnc hprev hj']
        have hd0 : (os p hp).get ⟨0, hprev⟩ * ((os p hp).get ⟨1, hj'⟩)⁻¹ = d := by
          simp [d]
        rw [hS0, hd0]
        simp [powSet_one, powSet_two]
      · have hj1 : 1 ≤ j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hj0)
        have hdj : (os p hp).get ⟨j, hprev⟩ * ((os p hp).get ⟨j + 1, hj'⟩)⁻¹ = d :=
          S_succ_dj_eq_d p hp hfirst hnc hprev hj' d hd_ne hj1 hS_j
        have hcardPow : (powSet d (j + 1)).card = j + 1 := by
          rw [← hS_j]
          exact S_card p hp hfirst hnc hprev
        rw [S_succ p hp hfirst hnc hprev hj']
        rw [hS_j, hdj]
        exact powSet_succ d hcardPow

/-- A finite group of cardinality at most one is cyclic. -/
lemma isCyclic_of_card_le_one (h : Fintype.card G ≤ 1) : IsCyclic G := by
  refine ⟨1, ?_⟩
  intro x
  have hx : x = 1 := (Fintype.card_le_one_iff.mp h) x 1
  exact ⟨0, by simpa [hx]⟩

/-- A common non-crossing order of the Cayley matchings forces `G` to be
cyclic. -/
theorem noncrossing_order_cyclic (p : Point G → ℕ) (hp : Function.Injective p)
    (hfirst : p (E 1) = 0)
    (hnc : ∀ g x, x ≠ 1 → ¬ Cross (p (E 1)) (p (O g)) (p (E x)) (p (O (x * g)))) :
    IsCyclic G := by
  by_cases hn1 : Fintype.card G ≤ 1
  · exact isCyclic_of_card_le_one hn1
  · have hn2 : 2 ≤ Fintype.card G := by omega
    have hcard : (os p hp).length = Fintype.card G := os_length p hp
    rcases S_pow p hp hfirst hnc hcard hn2 with ⟨d, hd_ne, hS⟩
    have hlast : Fintype.card G - 1 < (os p hp).length := by
      rw [hcard]
      omega
    have hSlast : S p ((os p hp).get ⟨Fintype.card G - 1, hlast⟩) =
        powSet d (Fintype.card G) := by
      have hn1' : (Fintype.card G - 1) + 1 = Fintype.card G := by omega
      simpa [hn1'] using hS (Fintype.card G - 1) hlast
    have hcardS : (S p ((os p hp).get ⟨Fintype.card G - 1, hlast⟩)).card =
        Fintype.card G := by
      rw [S_card p hp hfirst hnc hlast]
      omega
    have hcardPow : (powSet d (Fintype.card G)).card = Fintype.card G := by
      rw [← hSlast]
      exact hcardS
    have hEqUniv : powSet d (Fintype.card G) = Finset.univ :=
      Finset.eq_univ_of_card _ hcardPow
    refine ⟨d, ?_⟩
    intro x
    have hxS : x ∈ S p ((os p hp).get ⟨Fintype.card G - 1, hlast⟩) := by
      rw [hSlast, hEqUniv]
      simp
    rw [hSlast] at hxS
    rcases powSet_mem d hxS with ⟨i, hi, hpow⟩
    exact ⟨(i : ℤ), by simpa [zpow_natCast] using hpow⟩

end FourXOR
end Research
end QIT

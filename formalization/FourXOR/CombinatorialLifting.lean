/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.Definitions

/-!
# FourXOR: the zigzag refutation for cyclic Cayley games

This file proves the constructive direction of the translation-matching
classification for `ZMod n`:
the Cayley game of every finite cyclic group has a true refutation, given
explicitly by the zigzag word.  The projection onto every player is a
concatenation of palindromic nested blocks, and each nested block reduces to
the empty word.
-/

open scoped BigOperators

namespace QIT
namespace Research
namespace FourXOR

variable {n : ℕ}

/-- Sum over a `flatMap`, for integer-valued lists. -/
lemma sum_flatMap {α : Type*} (f : α → List ℤ) (l : List α) :
    (l.flatMap f).sum = (l.map (fun a => (f a).sum)).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.sum_append, ih]

/-- Parity contribution of one zigzag pair. -/
lemma zigzagPairParity_sum (m t : ℕ) :
    ((zigzagPair (n := m) t).map parityInt).sum = if (t : ZMod m) = 0 then 1 else 0 := by
  simp [zigzagPair, parityInt, neg_eq_zero]

/-- The total parity of the zigzag word of order `m`. -/
def zigzagParitySum (m : ℕ) : ℤ := ((zigzag (n := m)).map parityInt).sum

/-- In a range of length `m` inside `ZMod N`, exactly the element `0`
contributes one. -/
lemma rangeParitySum_general (N m : ℕ) (hN : 0 < N) (hm : m ≤ N) :
    ((List.range m).map (fun t : ℕ => if (t : ZMod N) = 0 then (1 : ℤ) else 0)).sum =
      if m = 0 then (0 : ℤ) else 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [List.range_succ, List.map_append, List.sum_append]
      rw [ih (by omega)]
      by_cases hm : m = 0
      · subst m
        simp
      · have hz : ¬ ((m : ZMod N) = 0) := by
          intro h
          rw [ZMod.natCast_eq_zero_iff m N] at h
          exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) h
        simp [hz, hm]

/-- In a range of length `m`, exactly the element `0` contributes one. -/
lemma rangeParitySum (m : ℕ) :
    ((List.range m).map (fun t : ℕ => if (t : ZMod (m + 1)) = 0 then (1 : ℤ) else 0)).sum =
      if m = 0 then (0 : ℤ) else 1 := by
  exact rangeParitySum_general (m + 1) m (by omega) (by omega)

/-- The parity sum of the zigzag word is one for every positive order. -/
theorem zigzagParitySum_eq (m : ℕ) : zigzagParitySum m = if m = 0 then 0 else 1 := by
  induction m with
  | zero => simp [zigzagParitySum, zigzag, zigzagPair, parityInt]
  | succ m ih =>
      unfold zigzagParitySum
      rw [zigzag, List.range_succ, List.flatMap_append, List.flatMap_singleton,
        List.map_append, List.sum_append]
      rw [List.map_flatMap, sum_flatMap]
      simp_rw [zigzagPairParity_sum]
      have hlast : (if (m : ZMod (m + 1)) = 0 then (1 : ℤ) else 0) =
          if m = 0 then (1 : ℤ) else 0 := by
        by_cases hm : m = 0
        · subst m
          simp
        · have hz : ¬ ((m : ZMod (m + 1)) = 0) := by
            intro h
            rw [ZMod.natCast_eq_zero_iff m (m + 1)] at h
            exact (Nat.not_dvd_of_pos_of_lt (by omega) (by omega)) h
          simp [hz, hm]
      have hsum : ((List.range m).map (fun t : ℕ => if (t : ZMod (m + 1)) = 0 then (1 : ℤ) else 0)).sum =
          if m = 0 then (0 : ℤ) else 1 := rangeParitySum_general (m + 1) m (by omega) (by omega)
      rw [hsum, hlast]
      by_cases hm0 : m = 0
      · subst m
        norm_num
      · have hne : m + 1 ≠ 0 := by omega
        simp [hm0, hne]

/-- The zigzag word of a cyclic Cayley game has odd total parity. -/
theorem zigzag_parity_odd [NeZero n] :
    ((zigzag (n := n)).map parityInt).sum % 2 = 1 := by
  have h := zigzagParitySum_eq n
  unfold zigzagParitySum at h
  have hn : n ≠ 0 := NeZero.ne n
  simp [h, hn]

/-- The projection of a block `[lo, hi)` onto player `a`, built backwards
from the last pair. -/
def projRange (a : ZMod n) : (lo hi : ℕ) → List (ZMod n)
  | lo, hi =>
      if h : lo < hi then
        projRange a lo (hi - 1) ++ [((hi - 1 : ℕ) : ZMod n), -((hi - 1 : ℕ) : ZMod n) + a]
      else []
termination_by lo hi => hi - lo
decreasing_by omega

/-- The palindromic nested skeleton of a block `[lo, hi)`. -/
def blockProj : (lo hi : ℕ) → List (ZMod n)
  | lo, hi =>
      if h : lo < hi then
        if h' : lo + 1 < hi then
          (((lo : ZMod n) :: ((hi - 1 : ℕ) : ZMod n) :: blockProj (lo + 1) (hi - 1)) ++
            [((hi - 1 : ℕ) : ZMod n), (lo : ZMod n)])
        else [(lo : ZMod n), (lo : ZMod n)]
      else []
termination_by lo hi => hi - lo
decreasing_by omega

/-- The block projection removes its last pair. -/
theorem projRange_back (a : ZMod n) (lo hi : ℕ) (h : lo < hi) :
    projRange a lo hi =
      projRange a lo (hi - 1) ++ [((hi - 1 : ℕ) : ZMod n), -((hi - 1 : ℕ) : ZMod n) + a] := by
  rw [projRange]
  simp [h]

/-- The block projection starts with its first pair. -/
theorem projRange_front (a : ZMod n) (lo hi : ℕ) (h : lo < hi) :
    projRange a lo hi =
      ((lo : ZMod n) :: ((-(lo : ZMod n) + a) :: projRange a (lo + 1) hi)) := by
  refine @Nat.strong_induction_on
    (fun m : ℕ => ∀ lo' hi' : ℕ, hi' - lo' = m → lo' < hi' →
      projRange a lo' hi' = ((lo' : ZMod n) :: ((-(lo' : ZMod n) + a) :: projRange a (lo' + 1) hi')))
    (hi - lo) ?_ lo hi rfl h
  intro m ih lo' hi' hmeq hlt
  by_cases h2 : lo' + 1 < hi'
  · have hm' : (hi' - 1) - lo' < m := by omega
    rw [projRange_back a lo' hi' hlt]
    rw [ih ((hi' - 1) - lo') hm' lo' (hi' - 1) rfl (by omega)]
    rw [projRange_back a (lo' + 1) hi' h2]
    simp [List.append_assoc]
  · have hhi : hi' = lo' + 1 := by omega
    subst hi'
    rw [projRange_back a lo' (lo' + 1) (by omega)]
    simp [projRange]

/-- The block projection equals the explicit flatMap interleaving. -/
theorem projRange_eq_flatMap (a : ZMod n) (lo hi : ℕ) :
    projRange a lo hi =
      (List.range (hi - lo)).flatMap
        (fun k => [((lo + k : ℕ) : ZMod n), -((lo + k : ℕ) : ZMod n) + a]) := by
  refine @Nat.strong_induction_on
    (fun m : ℕ => ∀ lo' hi', hi' - lo' = m →
      projRange a lo' hi' =
        (List.range (hi' - lo')).flatMap
          (fun k => [((lo' + k : ℕ) : ZMod n), -((lo' + k : ℕ) : ZMod n) + a]))
    (hi - lo) ?_ lo hi rfl
  intro m ih lo' hi' hmeq
  by_cases h : lo' < hi'
  · have hm' : (hi' - 1) - lo' < m := by omega
    rw [projRange_back a lo' hi' h, ih ((hi' - 1) - lo') hm' lo' (hi' - 1) (by omega)]
    have hb : hi' - lo' = (hi' - 1 - lo') + 1 := by omega
    rw [hb, List.range_succ, List.flatMap_append, List.flatMap_singleton]
    congr 1
    have hlo : lo' ≤ hi' - 1 := by omega
    have hsum : lo' + (hi' - 1 - lo') = hi' - 1 := Nat.add_sub_of_le hlo
    rw [hsum]
  · have hb : hi' - lo' = 0 := by omega
    rw [hb]
    simp [projRange, h]

/-- The block projection splits at an intermediate point. -/
theorem projRange_split (a : ZMod n) (lo mid hi : ℕ) (hlo : lo ≤ mid) (hmid : mid ≤ hi) :
    projRange a lo hi = projRange a lo mid ++ projRange a mid hi := by
  refine @Nat.strong_induction_on
    (fun m : ℕ => ∀ mid' hi', hi' - mid' = m → lo ≤ mid' → mid' ≤ hi' →
      projRange a lo hi' = projRange a lo mid' ++ projRange a mid' hi')
    (hi - mid) ?_ mid hi rfl hlo hmid
  intro m ih mid' hi' hmeq hlo' hmid'
  by_cases h : mid' < hi'
  · have hm' : (hi' - 1) - mid' < m := by omega
    have hprev : projRange a lo (hi' - 1) =
        projRange a lo mid' ++ projRange a mid' (hi' - 1) :=
      ih ((hi' - 1) - mid') hm' mid' (hi' - 1) (by omega) hlo' (by omega)
    rw [projRange_back a lo hi' (by omega), projRange_back a mid' hi' h, hprev]
    rw [← List.append_assoc]
  · have hhi : mid' = hi' := by omega
    subst hi'
    have hmid'' : projRange a mid' mid' = [] := by
      rw [projRange]
      simp
    rw [hmid'']
    simp

/-- A block whose letters satisfy the reflection closure is a palindrome
with nested pairings. -/
theorem blockProj_nested (lo hi : ℕ) : NestedWord (blockProj (n := n) lo hi) := by
  refine @Nat.strong_induction_on
    (fun m : ℕ => ∀ lo' hi', hi' - lo' = m → NestedWord (blockProj (n := n) lo' hi'))
    (hi - lo) ?_ lo hi rfl
  intro m ih lo' hi' hmeq
  by_cases h : lo' < hi'
  · by_cases h' : lo' + 1 < hi'
    · have hm' : (hi' - 1) - (lo' + 1) < m := by omega
      have hmid : NestedWord (blockProj (n := n) (lo' + 1) (hi' - 1)) :=
        ih ((hi' - 1) - (lo' + 1)) hm' (lo' + 1) (hi' - 1) (by omega)
      have h1 : NestedWord
          ([((hi' - 1 : ℕ) : ZMod n)] ++ blockProj (n := n) (lo' + 1) (hi' - 1) ++
            [((hi' - 1 : ℕ) : ZMod n)]) :=
        NestedWord.pair ((hi' - 1 : ℕ) : ZMod n) (blockProj (n := n) (lo' + 1) (hi' - 1)) hmid
      have h2 : NestedWord
          ((lo' : ZMod n) :: (([((hi' - 1 : ℕ) : ZMod n)] ++
            blockProj (n := n) (lo' + 1) (hi' - 1) ++
            [((hi' - 1 : ℕ) : ZMod n)]) ++ [(lo' : ZMod n)])) :=
        NestedWord.pair (lo' : ZMod n)
          ([((hi' - 1 : ℕ) : ZMod n)] ++ blockProj (n := n) (lo' + 1) (hi' - 1) ++
            [((hi' - 1 : ℕ) : ZMod n)])
          h1
      rw [blockProj]
      simpa [h, h', List.append_assoc] using h2
    · have hhi : hi' = lo' + 1 := by omega
      subst hi'
      rw [blockProj]
      simpa using (NestedWord.pair (lo' : ZMod n) [] NestedWord.nil)
  · rw [blockProj]
    simpa [h] using (NestedWord.nil : NestedWord ([] : List (ZMod n)))

/-- Closure of the first block `[0, a.val+1)`. -/
lemma blockA_closure (a : ZMod n) [NeZero n] {t : ℕ} (ht : t < a.val + 1) :
    -((t : ZMod n)) + a = ((0 + (a.val + 1) - 1 - t : ℕ) : ZMod n) := by
  rw [← ZMod.natCast_zmod_val a]
  have hval : (↑(a.val) : ZMod n).val = a.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (ZMod.val_lt a)
  rw [hval]
  have hn : (0 + (a.val + 1) - 1 - t : ℕ) = a.val - t := by omega
  rw [hn]
  have htle : t ≤ a.val := by omega
  have h' : ((a.val - t : ℕ) : ZMod n) = (a.val : ZMod n) - (t : ZMod n) := by
    have hsum' : (a.val : ZMod n) = ((a.val - t : ℕ) : ZMod n) + (t : ZMod n) := by
      rw [← Nat.cast_add]
      congr 1
      exact (Nat.sub_add_cancel htle).symm
    exact (sub_eq_iff_eq_add.mpr hsum').symm
  rw [add_comm, ← sub_eq_add_neg, ← h']

/-- Closure of the second block `[a.val+1, n)`. -/
lemma blockB_closure (a : ZMod n) [NeZero n] {t : ℕ} (ht1 : a.val + 1 ≤ t) (ht2 : t < n) :
    -((t : ZMod n)) + a = (((a.val + 1) + n - 1 - t : ℕ) : ZMod n) := by
  rw [← ZMod.natCast_zmod_val a]
  have hval : (↑(a.val) : ZMod n).val = a.val := by
    rw [ZMod.val_natCast]
    exact Nat.mod_eq_of_lt (ZMod.val_lt a)
  rw [hval]
  have hn : ((a.val + 1) + n - 1 - t : ℕ) = a.val + n - t := by omega
  rw [hn]
  have h' : ((a.val + n - t : ℕ) : ZMod n) = (a.val : ZMod n) - (t : ZMod n) := by
    have hsum' : ((a.val + n - t : ℕ) : ZMod n) + (t : ZMod n) = (a.val : ZMod n) := by
      rw [← Nat.cast_add]
      have hstep : (a.val + n - t) + t = a.val + n := by
        exact Nat.sub_add_cancel (by omega : t ≤ a.val + n)
      rw [hstep]
      rw [Nat.cast_add, ZMod.natCast_self]
      simp
    exact (sub_eq_iff_eq_add.mpr hsum'.symm).symm
  rw [add_comm, ← sub_eq_add_neg, ← h']

/-- A reflected block equals its palindromic skeleton. -/
theorem blockProj_eq_projRange (a : ZMod n) (lo hi : ℕ)
    (hcl : ∀ t : ℕ, lo ≤ t → t < hi →
      -((t : ZMod n)) + a = ((lo + hi - 1 - t : ℕ) : ZMod n)) :
    blockProj (n := n) lo hi = projRange a lo hi := by
  refine @Nat.strong_induction_on
    (fun m : ℕ => ∀ lo' hi', hi' - lo' = m →
      (∀ t : ℕ, lo' ≤ t → t < hi' →
        -((t : ZMod n)) + a = ((lo' + hi' - 1 - t : ℕ) : ZMod n)) →
      blockProj (n := n) lo' hi' = projRange a lo' hi')
    (hi - lo) ?_ lo hi rfl hcl
  intro m ih lo' hi' hmeq hcl'
  by_cases h : lo' < hi'
  · by_cases h' : lo' + 1 < hi'
    · have hm' : (hi' - 1) - (lo' + 1) < m := by omega
      have hih : blockProj (n := n) (lo' + 1) (hi' - 1) = projRange a (lo' + 1) (hi' - 1) :=
        ih ((hi' - 1) - (lo' + 1)) hm' (lo' + 1) (hi' - 1) (by omega) (by
          intro t ht1 ht2
          have hc := hcl' t (by omega) (by omega)
          have hn : (lo' + hi' - 1 - t : ℕ) = ((lo' + 1) + (hi' - 1) - 1 - t) := by omega
          simpa [hn] using hc)
      have hclo : -((lo' : ZMod n)) + a = ((hi' - 1 : ℕ) : ZMod n) := by
        have hc := hcl' lo' (by omega) (by omega)
        have hn : (lo' + hi' - 1 - lo' : ℕ) = hi' - 1 := by omega
        simpa [hn] using hc
      have hcHi : -(((hi' - 1 : ℕ) : ZMod n)) + a = (lo' : ZMod n) := by
        have hc := hcl' (hi' - 1) (by omega) (by omega)
        have hn : (lo' + hi' - 1 - (hi' - 1) : ℕ) = lo' := by omega
        simpa [hn] using hc
      rw [blockProj]
      simp [h, h']
      rw [projRange_back a lo' hi' h]
      rw [hih, projRange_front a lo' (hi' - 1) (by omega), hclo, hcHi]
      simp [blockProj, List.append_assoc]
    · have hhi : hi' = lo' + 1 := by omega
      subst hi'
      rw [projRange_back a lo' (lo' + 1) (by omega)]
      have hclo : -((lo' : ZMod n)) + a = (lo' : ZMod n) := by
        have h' := hcl' lo' (by omega) (by omega)
        have hn : (lo' + (lo' + 1) - 1 - lo' : ℕ) = lo' := by omega
        simpa [hn] using h'
      have hn2 : (lo' + 1 - 1 : ℕ) = lo' := by omega
      simp [blockProj, projRange, hclo, hn2]
  · simp [blockProj, projRange, h]

/-- The projection of the zigzag splits into the two reflected blocks. -/
theorem projectionZigzag_split (a : ZMod n) [NeZero n] :
    projectionZigzag (n := n) a =
      blockProj (n := n) 0 (a.val + 1) ++ blockProj (n := n) (a.val + 1) n := by
  set b := a.val + 1
  have hb1 : 0 ≤ b := by omega
  have hb2 : b ≤ n := by
    have hval : a.val < n := ZMod.val_lt a
    omega
  have hpr : projectionZigzag (n := n) a = projRange a 0 n := by
    change (List.range n).flatMap (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + a]) =
      projRange a 0 n
    simpa using (projRange_eq_flatMap a 0 n).symm
  rw [hpr]
  have hsplit : projRange a 0 n = projRange a 0 b ++ projRange a b n :=
    projRange_split a 0 b n hb1 hb2
  have hA : projRange a 0 b = blockProj (n := n) 0 b := by
    exact (blockProj_eq_projRange (a := a) 0 b (by
      intro t ht1 ht2
      simpa [b] using (blockA_closure (a := a) ht2))).symm
  have hB : projRange a b n = blockProj (n := n) b n := by
    exact (blockProj_eq_projRange (a := a) b n (by
      intro t ht1 ht2
      simpa [b] using (blockB_closure (a := a) ht1 ht2))).symm
  rw [hsplit, hA, hB]

/-- The main theorem: the Cayley game of a finite cyclic group has a true
refutation, given by the zigzag word. -/
theorem cyclic_cayley_has_true_refutation [NeZero n] :
    ∃ w : List (Clause n), IsTrueRefutation (n := n) w := by
  refine ⟨zigzag (n := n), ?_⟩
  constructor
  · intro α
    rw [projection_zigzag α, projectionZigzag_split α]
    exact ReducesTo.append
      (NestedWord.reducible (blockProj_nested (n := n) 0 (α.val + 1)))
      (NestedWord.reducible (blockProj_nested (n := n) (α.val + 1) n))
  · exact zigzag_parity_odd (n := n)

/-- In the Cayley game of a finite cyclic group, every PREF lifts to a true
refutation (the zigzag word). -/
theorem cyclic_cayley_pref_lifts [NeZero n] :
    (∃ z : Clause n → ℤ, IsPREF (n := n) z) →
      ∃ w : List (Clause n), IsTrueRefutation (n := n) w := by
  intro _
  exact cyclic_cayley_has_true_refutation (n := n)

/-- The standard `-E + O` weighting is a PREF of the Cayley game. -/
theorem standardZ_isPREF [NeZero n] : IsPREF (n := n) (standardZ (n := n)) := by
  constructor
  · intro α q
    have hsum1 : (∑ x : ZMod n, if x = q then (-1 : ℤ) else 0) = -1 := by
      rw [Fintype.sum_eq_single q (fun x hx => by simp [hx])]
      simp
    have hsum2 : (∑ x : ZMod n, if x + α = q then (1 : ℤ) else 0) = 1 := by
      rw [Fintype.sum_eq_single (q - α) (fun x hx => by
        have h' : x + α ≠ q := by
          intro h
          apply hx
          have h'' := congrArg (fun y : ZMod n => y - α) h
          simpa [add_sub_cancel] using h''
        simp [h'])]
      simp [sub_add_cancel]
    simp [localBalance, standardZ, letter, Fintype.sum_prod_type, Fintype.sum_bool,
      Finset.sum_add_distrib, hsum1, hsum2]
  · have hsum : (∑ x : ZMod n, if x = 0 then (1 : ℤ) else 0) = 1 := by
      rw [Fintype.sum_eq_single 0 (fun x hx => by simp [hx])]
      simp
    simp [IsPREF, standardZ, parityInt, Fintype.sum_prod_type, Fintype.sum_bool, hsum]

end FourXOR
end Research
end QIT

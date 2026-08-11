/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.Definitions

/-!
# FourXOR: all-length obstruction — combinatorial core

The all-length no-refutation theorem is proved by
extracting degree-one and class-two necessary conditions from a reducible
projection word.  This file develops those conditions combinatorially:
free reduction of a word over involutions preserves the alternating letter
sums and the signed ordered pair counts, so any reducible word has all
alternating sums zero and all class-two pair counts zero.  No free-group
machinery is required.
-/

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*}

/-- Alternating signed sum of the positions of letter `q` in `w`
(`+1, -1, +1, ...`). -/
def altSum [DecidableEq G] : List G → G → ℤ
  | [], q => 0
  | a :: l, q => (if a = q then 1 else 0) - altSum l q

/-- Alternating signed sum of the positions satisfying `P`. -/
def signedSum {α : Type*} (w : List α) (P : α → Prop) [DecidablePred P] : ℤ :=
  match w with
  | [] => 0
  | a :: l => (if P a then 1 else 0) - signedSum l P

/-- Signed ordered pair count `Σ_{p<q} s_p s_q [w_p=i][w_q=j]`. -/
def pairSum [DecidableEq G] : List G → G → G → ℤ
  | [], i, j => 0
  | a :: l, i, j => (if a = i then 1 else 0) * (- altSum l j) + pairSum l i j

/-- Signed ordered pair count for two predicates on a clause word. -/
def pairSumClause {α : Type*} (w : List α) (P Q : α → Prop)
    [DecidablePred P] [DecidablePred Q] : ℤ :=
  match w with
  | [] => 0
  | a :: l => (if P a then 1 else 0) * (- signedSum l Q) + pairSumClause l P Q

/-- `altSum` over an append. -/
lemma altSum_append [DecidableEq G] (l r : List G) (q : G) :
    altSum (l ++ r) q = altSum l q + (-1 : ℤ) ^ l.length * altSum r q := by
  induction l with
  | nil => simp [altSum]
  | cons a l ih =>
      simp only [List.cons_append, altSum]
      rw [ih]
      have hlen : (a :: l).length = l.length + 1 := by simp
      have hp : (-1 : ℤ) ^ (l.length + 1) = - ((-1 : ℤ) ^ l.length) := by
        rw [pow_succ]
        ring
      rw [hlen, hp]
      ring

/-- `signedSum` over an append. -/
lemma signedSum_append {α : Type*} (l r : List α) (P : α → Prop) [DecidablePred P] :
    signedSum (l ++ r) P = signedSum l P + (-1 : ℤ) ^ l.length * signedSum r P := by
  induction l with
  | nil => simp [signedSum]
  | cons a l ih =>
      simp only [List.cons_append, signedSum]
      rw [ih]
      have hlen : (a :: l).length = l.length + 1 := by simp
      have hp : (-1 : ℤ) ^ (l.length + 1) = - ((-1 : ℤ) ^ l.length) := by
        rw [pow_succ]
        ring
      rw [hlen, hp]
      ring

/-- `altSum` commutes with `map` through `signedSum`. -/
lemma altSum_map {H : Type*} [DecidableEq H] (f : G → H) [DecidableEq G]
    (w : List G) (q : H) :
    altSum (w.map f) q = signedSum w (fun a => f a = q) := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp [altSum, signedSum, ih]

/-- `signedSum` commutes with `map`. -/
lemma signedSum_map {α β : Type*} (f : α → β) (w : List α) (P : β → Prop)
    [DecidableEq β] [DecidablePred P] :
    signedSum (w.map f) P = signedSum w (fun a => P (f a)) := by
  induction w with
  | nil => rfl
  | cons a l ih => simp [signedSum, ih]

/-- `pairSum` over an append. -/
lemma pairSum_append [DecidableEq G] (l r : List G) (i j : G) :
    pairSum (l ++ r) i j =
      pairSum l i j + pairSum r i j + altSum l i * ((-1 : ℤ) ^ l.length * altSum r j) := by
  induction l with
  | nil => simp [pairSum, altSum]
  | cons a l ih =>
      simp only [List.cons_append, pairSum, altSum]
      rw [ih, altSum_append]
      have hlen : (a :: l).length = l.length + 1 := by simp
      have hp : (-1 : ℤ) ^ (l.length + 1) = - ((-1 : ℤ) ^ l.length) := by
        rw [pow_succ]
        ring
      rw [hlen, hp]
      ring

/-- `pairSum` commutes with `map` through `pairSumClause`. -/
lemma pairSum_map {H : Type*} [DecidableEq H] (f : G → H) [DecidableEq G]
    (w : List G) (i j : H) :
    pairSum (w.map f) i j =
      pairSumClause w (fun a => f a = i) (fun a => f a = j) := by
  induction w with
  | nil => rfl
  | cons a l ih =>
      simp [pairSum, pairSumClause, altSum_map, ih]

/-- The alternating sum of a repeated pair vanishes. -/
lemma altSum_pair_zero [DecidableEq G] (a q : G) : altSum [a, a] q = 0 := by
  simp [altSum]

/-- The pair count of a repeated pair vanishes for distinct letters. -/
lemma pairSum_pair_zero [DecidableEq G] (a : G) {i j : G} (hij : i ≠ j) :
    pairSum [a, a] i j = 0 := by
  simp only [pairSum, altSum]
  by_cases h1 : a = i <;> by_cases h2 : a = j
  · have h : i = j := h1.symm.trans h2
    exact False.elim (hij h)
  · simp [if_pos h1, if_neg h2]
  · simp [if_neg h1, if_pos h2]
  · simp [if_neg h1, if_neg h2]

/-- A single deletion step preserves every alternating letter sum. -/
lemma altSum_step [DecidableEq G] {w w' : List G} (h : Step w w') (q : G) :
    altSum w q = altSum w' q := by
  rcases h with ⟨l, r, a, hw, hw'⟩
  subst w
  subst w'
  rw [altSum_append, altSum_append]
  have hmid : altSum [a, a] q = 0 := altSum_pair_zero a q
  have hlen : (l ++ [a, a]).length = l.length + 2 := by simp
  have hp : (-1 : ℤ) ^ (l.length + 2) = (-1 : ℤ) ^ l.length := by
    rw [pow_add, pow_two]
    norm_num
  rw [hmid, hlen, hp]
  rw [altSum_append]
  ring_nf

/-- A single deletion step preserves every class-two pair count. -/
lemma pairSum_step [DecidableEq G] {w w' : List G} {i j : G} (hij : i ≠ j)
    (h : Step w w') : pairSum w i j = pairSum w' i j := by
  rcases h with ⟨l, r, a, hw, hw'⟩
  subst w
  subst w'
  rw [pairSum_append, pairSum_append]
  rw [pairSum_append, altSum_append]
  have hp1 : pairSum [a, a] i j = 0 := pairSum_pair_zero a hij
  have hp2 : altSum [a, a] j = 0 := altSum_pair_zero a j
  have hp3 : altSum [a, a] i = 0 := altSum_pair_zero a i
  rw [hp1, hp2, hp3]
  have hlen : (l ++ [a, a]).length = l.length + 2 := by simp
  have hp : (-1 : ℤ) ^ (l.length + 2) = (-1 : ℤ) ^ l.length := by
    rw [pow_add, pow_two]
    norm_num
  rw [hlen, hp]
  ring_nf

/-- Reduction preserves every alternating letter sum. -/
theorem altSum_reducesTo [DecidableEq G] {w w' : List G} (h : ReducesTo w w')
    (q : G) : altSum w q = altSum w' q := by
  induction h with
  | refl => rfl
  | tail htail hstep ih => exact ih.trans (altSum_step hstep q)

/-- Reduction preserves every class-two pair count. -/
theorem pairSum_reducesTo [DecidableEq G] {w w' : List G} {i j : G} (hij : i ≠ j)
    (h : ReducesTo w w') : pairSum w i j = pairSum w' i j := by
  induction h with
  | refl => rfl
  | tail htail hstep ih => exact ih.trans (pairSum_step hij hstep)

/-- A reducible word has every alternating letter sum zero. -/
theorem altSum_reducible [DecidableEq G] {w : List G} (h : Reducible w) (q : G) :
    altSum w q = 0 := by
  simpa using altSum_reducesTo h q

/-- A reducible word has every class-two pair count zero. -/
theorem pairSum_reducible [DecidableEq G] {w : List G} {i j : G} (hij : i ≠ j)
    (h : Reducible w) : pairSum w i j = 0 := by
  simpa using pairSum_reducesTo hij h

end FourXOR
end Research
end QIT

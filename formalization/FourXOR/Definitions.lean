/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import QIT

/-!
# FourXOR: definitions for the Cayley-game lifting theorem

This is the theorem-specific development for the translation-matching
classification: the Cayley game of a finite cyclic group admits a true refutation.
Only the constructive direction (zigzag word) and the finite-dimensional
quantum corollary are formalized; no general XOR-game base layer is built.

The group is represented by `ZMod n`, the standard model of a finite cyclic
group of order `n`.
-/

open scoped BigOperators

namespace QIT
namespace Research
namespace FourXOR

universe u

variable {n : ℕ}

/-- A clause of the Cayley game: `(g, false)` is `E_g` and `(g, true)` is `O_g`. -/
abbrev Clause (n : ℕ) := ZMod n × Bool

/-- The letter received by player `α` from clause `c`. -/
def letter (c : Clause n) (α : ZMod n) : ZMod n :=
  if c.2 then c.1 + α else c.1

/-- Target parity of a clause, as an integer: only `O_0` carries bit `1`. -/
def parityInt (c : Clause n) : ℤ :=
  if c.2 ∧ c.1 = 0 then 1 else 0

/-- Projection of a clause word onto player `α`. -/
def projection (w : List (Clause n)) (α : ZMod n) : List (ZMod n) :=
  w.map (fun c => letter c α)

/-- One reduction step: delete an adjacent equal pair. -/
def Step {α : Type u} (w w' : List α) : Prop :=
  ∃ (l r : List α) (a : α), w = l ++ [a, a] ++ r ∧ w' = l ++ r

/-- `w` reduces to `w'` by a finite sequence of adjacent-pair deletions. -/
abbrev ReducesTo {α : Type u} (w w' : List α) : Prop :=
  Relation.ReflTransGen (Step (α := α)) w w'

/-- `w` freely reduces to the empty word.  This is exactly reduction in the
free product of the question groups `Z₂` (each question letter is an
involution). -/
def Reducible {α : Type u} (w : List α) : Prop :=
  ReducesTo w []

/-- A word whose equal-letter pairings are all nested or disjoint
(a concatenation of palindromic blocks). -/
inductive NestedWord {α : Type u} : List α → Prop where
  | nil : NestedWord []
  | pair : ∀ (a : α) (mid : List α), NestedWord mid → NestedWord (a :: mid ++ [a])
  | concat : ∀ {l r : List α}, NestedWord l → NestedWord r → NestedWord (l ++ r)

/-- A true refutation: every player projection freely reduces to the empty
word, and the total target parity is odd. -/
def IsTrueRefutation (w : List (Clause n)) : Prop :=
  (∀ α : ZMod n, Reducible (projection w α)) ∧ ((w.map parityInt).sum % 2 = 1)

/-- Signed balance of `z` at a player-question pair. -/
def localBalance [NeZero n] (z : Clause n → ℤ) (α q : ZMod n) : ℤ :=
  ∑ c : Clause n, z c * if letter c α = q then 1 else 0

/-- A PREF: integer balance at every player-question pair plus odd total
target parity. -/
def IsPREF [NeZero n] (z : Clause n → ℤ) : Prop :=
  (∀ α q : ZMod n, localBalance z α q = 0) ∧
    ((∑ c : Clause n, z c * parityInt c) % 2 = 1)

/-- The standard PREF weight: `-1` on every `E` and `+1` on every `O`. -/
def standardZ (c : Clause n) : ℤ :=
  if c.2 then 1 else -1

/-- The two clauses `E_t` and `O_{n-t}` of the zigzag word. -/
def zigzagPair (t : ℕ) : List (Clause n) :=
  [((t : ZMod n), false), ((-(t : ZMod n) : ZMod n), true)]

/-- The zigzag clause word `E_0 O_0 E_1 O_{n-1} ... E_{n-1} O_1`. -/
def zigzag : List (Clause n) :=
  (List.range n).flatMap zigzagPair

/-- The projection of the zigzag word onto player `α`, spelled out as the
interleaving `[0, α, 1, α-1, 2, α-2, ...]`. -/
def projectionZigzag (α : ZMod n) : List (ZMod n) :=
  (List.range n).flatMap (fun t : ℕ => [((t : ZMod n)), -((t : ZMod n)) + α])

@[simp]
theorem letter_E (g : ZMod n) (α : ZMod n) : letter (g, false) α = g := by
  simp [letter]

@[simp]
theorem letter_O (g : ZMod n) (α : ZMod n) : letter (g, true) α = g + α := by
  simp [letter]

@[simp]
theorem parityInt_E (g : ZMod n) : parityInt (g, false) = 0 := by
  simp [parityInt]

@[simp]
theorem parityInt_O_zero : parityInt ((0 : ZMod n), true) = 1 := by
  simp [parityInt]

@[simp]
theorem parityInt_O_ne_zero {g : ZMod n} (hg : g ≠ 0) : parityInt (g, true) = 0 := by
  simp [parityInt, hg]

/-- The projection of the zigzag word onto player `α` is the interleaving
`[0, α, 1, α-1, 2, α-2, ...]`. -/
theorem projection_zigzag (α : ZMod n) :
    projection (zigzag (n := n)) α = projectionZigzag (n := n) α := by
  unfold projection zigzag projectionZigzag
  rw [List.map_flatMap]
  simp [zigzagPair, letter]

/-- The zigzag word has length `2 n`. -/
theorem zigzag_length : (zigzag (n := n)).length = 2 * n := by
  simp [zigzag, zigzagPair, List.length_flatMap]
  omega

namespace ReducesTo

variable {α : Type u}

/-- Reduction steps can be performed inside any context. -/
theorem ctx {l r : List α} {m m' : List α} (h : ReducesTo m m') :
    ReducesTo (l ++ m ++ r) (l ++ m' ++ r) := by
  induction h generalizing l r with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail htail hstep ih =>
      rcases hstep with ⟨l', r', a, hb, hc⟩
      refine Relation.ReflTransGen.trans (ih (l := l) (r := r)) ?_
      rw [hb, hc]
      simpa [List.append_assoc] using
        (Relation.ReflTransGen.single
          ⟨l ++ l', r' ++ r, a, by simp [List.append_assoc], by simp [List.append_assoc]⟩)

/-- Reducibility of a concatenation. -/
theorem append {l r : List α} (hl : Reducible l) (hr : Reducible r) :
    Reducible (l ++ r) := by
  have h1 : ReducesTo (l ++ r) ([] ++ r) := by
    simpa using (ctx (l := []) (r := r) hl)
  exact Relation.ReflTransGen.trans h1 hr

/-- Reducibility of a word with a reducible middle block. -/
theorem mid {l m r : List α} (hm : Reducible m) (h : Reducible (l ++ r)) :
    Reducible (l ++ m ++ r) := by
  have h1 : ReducesTo (l ++ m ++ r) (l ++ [] ++ r) :=
    ctx (l := l) (r := r) hm
  exact Relation.ReflTransGen.trans (by simpa using h1) h

end ReducesTo

namespace NestedWord

/-- Every nested (palindromic) word freely reduces to the empty word. -/
theorem reducible {α : Type u} {w : List α} (h : NestedWord w) : Reducible w := by
  induction h with
  | nil =>
      exact Relation.ReflTransGen.refl
  | pair a mid hmid ih =>
      have hpair : Reducible ([a] ++ [a]) := by
        exact Relation.ReflTransGen.single ⟨[], [], a, by simp, by simp⟩
      exact ReducesTo.mid (l := [a]) (m := mid) (r := [a]) ih hpair
  | concat h1 h2 ih1 ih2 =>
      exact ReducesTo.append ih1 ih2

end NestedWord

end FourXOR
end Research
end QIT

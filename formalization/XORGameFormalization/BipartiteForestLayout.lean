/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.LinearForestOrder
public import Mathlib.Data.List.Monad

/-!
# Alternating layouts of finite bipartite linear forests

This file develops the list combinatorics used to concatenate the path
components of a bipartite linear forest.  Balanced components are oriented
positive-to-negative; positive-heavy and negative-heavy components are paired.
-/

@[expose] public section

namespace QIT
namespace XORGame

open scoped BigOperators

universe uP uN

noncomputable section

/-- Two signed vertices have opposite signs. -/
def OppositeSign {Positive : Type uP} {Negative : Type uN} :
    Positive ⊕ Negative → Positive ⊕ Negative → Prop
  | Sum.inl _, Sum.inr _ => True
  | Sum.inr _, Sum.inl _ => True
  | _, _ => False

theorem oppositeSign_symm
    {Positive : Type uP} {Negative : Type uN}
    {left right : Positive ⊕ Negative} :
    OppositeSign left right → OppositeSign right left := by
  cases left <;> cases right <;> simp [OppositeSign]

/-- Read a list of positive-negative pairs as a sign-alternating word. -/
def positiveNegativeWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Positive × Negative)) : List (Positive ⊕ Negative) :=
  pairs.flatMap fun pair => [Sum.inl pair.1, Sum.inr pair.2]

/-- Read a list of negative-positive pairs as a sign-alternating word. -/
def negativePositiveWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) : List (Positive ⊕ Negative) :=
  pairs.flatMap fun pair => [Sum.inr pair.1, Sum.inl pair.2]

/--
An alternating word beginning positively is either balanced and ends
negatively, or has one extra final positive vertex.
-/
theorem oppositeSign_chain_from_positive_decompose
    {Positive : Type uP} {Negative : Type uN}
    (positive : Positive) :
    ∀ tail : List (Positive ⊕ Negative),
      List.IsChain OppositeSign (Sum.inl positive :: tail) →
      (∃ pairs : List (Positive × Negative),
          pairs ≠ [] ∧
            Sum.inl positive :: tail = positiveNegativeWord pairs) ∨
        ∃ (pairs : List (Positive × Negative)) (last : Positive),
          Sum.inl positive :: tail =
            positiveNegativeWord pairs ++ [Sum.inl last]
  | [], _ => Or.inr ⟨[], positive, rfl⟩
  | Sum.inl other :: tail, hchain => by
      exact False.elim (by simpa [OppositeSign] using hchain.rel)
  | Sum.inr negative :: [], _ => by
      exact Or.inl ⟨[(positive, negative)], by simp, rfl⟩
  | Sum.inr negative :: Sum.inr other :: tail, hchain => by
      exact False.elim (by simpa [OppositeSign] using hchain.tail.rel)
  | Sum.inr negative :: Sum.inl next :: tail, hchain => by
      rcases oppositeSign_chain_from_positive_decompose
          next tail hchain.tail.tail with hbalanced | hheavy
      · obtain ⟨pairs, hpairs, hword⟩ := hbalanced
        exact Or.inl ⟨(positive, negative) :: pairs, by simp,
          by simp [positiveNegativeWord, hword]⟩
      · obtain ⟨pairs, last, hword⟩ := hheavy
        exact Or.inr ⟨(positive, negative) :: pairs, last,
          by simp [positiveNegativeWord, hword]⟩
termination_by tail => tail.length

/--
An alternating word beginning negatively is either balanced and ends
positively, or has one extra final negative vertex.
-/
theorem oppositeSign_chain_from_negative_decompose
    {Positive : Type uP} {Negative : Type uN}
    (negative : Negative) :
    ∀ tail : List (Positive ⊕ Negative),
      List.IsChain OppositeSign (Sum.inr negative :: tail) →
      (∃ pairs : List (Negative × Positive),
          pairs ≠ [] ∧
            Sum.inr negative :: tail = negativePositiveWord pairs) ∨
        ∃ (pairs : List (Negative × Positive)) (last : Negative),
          Sum.inr negative :: tail =
            negativePositiveWord pairs ++ [Sum.inr last]
  | [], _ => Or.inr ⟨[], negative, rfl⟩
  | Sum.inr other :: tail, hchain => by
      exact False.elim (by simpa [OppositeSign] using hchain.rel)
  | Sum.inl positive :: [], _ => by
      exact Or.inl ⟨[(negative, positive)], by simp, rfl⟩
  | Sum.inl positive :: Sum.inl other :: tail, hchain => by
      exact False.elim (by simpa [OppositeSign] using hchain.tail.rel)
  | Sum.inl positive :: Sum.inr next :: tail, hchain => by
      rcases oppositeSign_chain_from_negative_decompose
          next tail hchain.tail.tail with hbalanced | hheavy
      · obtain ⟨pairs, hpairs, hword⟩ := hbalanced
        exact Or.inl ⟨(negative, positive) :: pairs, by simp,
          by simp [negativePositiveWord, hword]⟩
      · obtain ⟨pairs, last, hword⟩ := hheavy
        exact Or.inr ⟨(negative, positive) :: pairs, last,
          by simp [negativePositiveWord, hword]⟩
termination_by tail => tail.length

/-- Signed mass: `+1` on the positive side and `-1` on the negative side. -/
def sideWeight {Positive : Type uP} {Negative : Type uN} :
    Positive ⊕ Negative → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- A nonempty alternating block running from positive to negative. -/
def IsPositiveNegativeBlock
    {Positive : Type uP} {Negative : Type uN}
    (order : List (Positive ⊕ Negative)) : Prop :=
  List.IsChain OppositeSign order ∧
    (∃ (positive : Positive) (tail : List (Positive ⊕ Negative)),
      order = Sum.inl positive :: tail) ∧
    ∃ (initial : List (Positive ⊕ Negative)) (negative : Negative),
      order = initial ++ [Sum.inr negative]

/-- A nonempty alternating block with one extra positive endpoint. -/
def IsPositiveHeavyBlock
    {Positive : Type uP} {Negative : Type uN}
    (order : List (Positive ⊕ Negative)) : Prop :=
  List.IsChain OppositeSign order ∧
    (∃ (positive : Positive) (tail : List (Positive ⊕ Negative)),
      order = Sum.inl positive :: tail) ∧
    ∃ (initial : List (Positive ⊕ Negative)) (positive : Positive),
      order = initial ++ [Sum.inl positive]

/-- A nonempty alternating block with one extra negative endpoint. -/
def IsNegativeHeavyBlock
    {Positive : Type uP} {Negative : Type uN}
    (order : List (Positive ⊕ Negative)) : Prop :=
  List.IsChain OppositeSign order ∧
    (∃ (negative : Negative) (tail : List (Positive ⊕ Negative)),
      order = Sum.inr negative :: tail) ∧
    ∃ (initial : List (Positive ⊕ Negative)) (negative : Negative),
      order = initial ++ [Sum.inr negative]

/-- Concatenating two positive-to-negative blocks preserves their form. -/
theorem IsPositiveNegativeBlock.append
    {Positive : Type uP} {Negative : Type uN}
    {left right : List (Positive ⊕ Negative)}
    (hleft : IsPositiveNegativeBlock left)
    (hright : IsPositiveNegativeBlock right) :
    IsPositiveNegativeBlock (left ++ right) := by
  rcases hleft with ⟨hleftChain, ⟨leftPositive, leftTail, hleftStart⟩,
    leftInitial, leftNegative, hleftEnd⟩
  rcases hright with ⟨hrightChain, ⟨rightPositive, rightTail, hrightStart⟩,
    rightInitial, rightNegative, hrightEnd⟩
  refine ⟨?_, ?_, ?_⟩
  · apply hleftChain.append hrightChain
    intro last hlast first hfirst
    have hlastEq : last = Sum.inr leftNegative := by
      simpa [hleftEnd] using hlast.symm
    have hfirstEq : first = Sum.inl rightPositive := by
      rw [hrightStart] at hfirst
      simpa using hfirst.symm
    subst last
    subst first
    trivial
  · exact ⟨leftPositive, leftTail ++ right, by simp [hleftStart]⟩
  · exact ⟨left ++ rightInitial, rightNegative, by
      rw [hrightEnd, List.append_assoc]⟩

/-- Pairing a positive-heavy block with a negative-heavy block makes a balanced block. -/
theorem IsPositiveHeavyBlock.append_negativeHeavy
    {Positive : Type uP} {Negative : Type uN}
    {left right : List (Positive ⊕ Negative)}
    (hleft : IsPositiveHeavyBlock left)
    (hright : IsNegativeHeavyBlock right) :
    IsPositiveNegativeBlock (left ++ right) := by
  rcases hleft with ⟨hleftChain, ⟨leftPositive, leftTail, hleftStart⟩,
    leftInitial, leftLast, hleftEnd⟩
  rcases hright with ⟨hrightChain, ⟨rightFirst, rightTail, hrightStart⟩,
    rightInitial, rightLast, hrightEnd⟩
  refine ⟨?_, ?_, ?_⟩
  · apply hleftChain.append hrightChain
    intro last hlast first hfirst
    have hlastEq : last = Sum.inl leftLast := by
      simpa [hleftEnd] using hlast.symm
    have hfirstEq : first = Sum.inr rightFirst := by
      rw [hrightStart] at hfirst
      simpa using hfirst.symm
    subst last
    subst first
    trivial
  · exact ⟨leftPositive, leftTail ++ right, by simp [hleftStart]⟩
  · exact ⟨left ++ rightInitial, rightLast, by
      rw [hrightEnd, List.append_assoc]⟩

/-- Flattening a nonempty list of balanced blocks gives one balanced block. -/
theorem isPositiveNegativeBlock_flatten
    {Positive : Type uP} {Negative : Type uN}
    (blocks : List (List (Positive ⊕ Negative)))
    (hne : blocks ≠ [])
    (hblocks : ∀ block ∈ blocks, IsPositiveNegativeBlock block) :
    IsPositiveNegativeBlock blocks.flatten := by
  induction blocks with
  | nil => exact False.elim (hne rfl)
  | cons block blocks ih =>
      by_cases hrest : blocks = []
      · subst blocks
        simpa using hblocks block (by simp)
      · rw [List.flatten_cons]
        exact (hblocks block (by simp)).append
          (ih hrest (fun other hother => hblocks other (by simp [hother])))

/-- Flattening any list of balanced blocks is sign-alternating. -/
theorem isChain_flatten_positiveNegativeBlocks
    {Positive : Type uP} {Negative : Type uN}
    (blocks : List (List (Positive ⊕ Negative)))
    (hblocks : ∀ block ∈ blocks, IsPositiveNegativeBlock block) :
    List.IsChain OppositeSign blocks.flatten := by
  by_cases hne : blocks = []
  · subst blocks
    exact .nil
  · exact (isPositiveNegativeBlock_flatten blocks hne hblocks).1

@[simp]
theorem sideWeight_sum_positiveNegativeWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Positive × Negative)) :
    ((positiveNegativeWord pairs).map sideWeight).sum = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [show positiveNegativeWord (pair :: pairs) =
        [Sum.inl pair.1, Sum.inr pair.2] ++
          positiveNegativeWord pairs by rfl]
      simp [sideWeight, ih]

@[simp]
theorem sideWeight_sum_negativePositiveWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) :
    ((negativePositiveWord pairs).map sideWeight).sum = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [show negativePositiveWord (pair :: pairs) =
        [Sum.inr pair.1, Sum.inl pair.2] ++
          negativePositiveWord pairs by rfl]
      simp [sideWeight, ih]

/-- Positive-negative pair words alternate in sign. -/
theorem positiveNegativeWord_isChain
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Positive × Negative)) :
    List.IsChain OppositeSign (positiveNegativeWord pairs) := by
  induction pairs with
  | nil => exact .nil
  | cons pair pairs ih =>
      cases pairs with
      | nil => simp [positiveNegativeWord, OppositeSign]
      | cons next rest =>
          have ih' := ih
          simp only [positiveNegativeWord, List.flatMap_cons]
          exact .cons_cons (by simp [OppositeSign]) <|
            .cons_cons (by simp [OppositeSign]) ih'

/-- Negative-positive pair words alternate in sign. -/
theorem negativePositiveWord_isChain
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) :
    List.IsChain OppositeSign (negativePositiveWord pairs) := by
  induction pairs with
  | nil => exact .nil
  | cons pair pairs ih =>
      cases pairs with
      | nil => simp [negativePositiveWord, OppositeSign]
      | cons next rest =>
          have ih' := ih
          simp only [negativePositiveWord, List.flatMap_cons]
          exact .cons_cons (by simp [OppositeSign]) <|
            .cons_cons (by simp [OppositeSign]) ih'

/-- A nonempty positive-negative pair word starts positively. -/
theorem positiveNegativeWord_starts
    {Positive : Type uP} {Negative : Type uN}
    {pairs : List (Positive × Negative)} (hpairs : pairs ≠ []) :
    ∃ (positive : Positive) (tail : List (Positive ⊕ Negative)),
      positiveNegativeWord pairs = Sum.inl positive :: tail := by
  obtain ⟨pair, pairs, rfl⟩ := List.exists_cons_of_ne_nil hpairs
  exact ⟨pair.1, Sum.inr pair.2 :: positiveNegativeWord pairs, rfl⟩

/-- A nonempty positive-negative pair word ends negatively. -/
theorem positiveNegativeWord_ends
    {Positive : Type uP} {Negative : Type uN}
    {pairs : List (Positive × Negative)} (hpairs : pairs ≠ []) :
    ∃ (initial : List (Positive ⊕ Negative)) (negative : Negative),
      positiveNegativeWord pairs = initial ++ [Sum.inr negative] := by
  induction pairs with
  | nil => exact False.elim (hpairs rfl)
  | cons pair pairs ih =>
      by_cases hrest : pairs = []
      · subst pairs
        exact ⟨[Sum.inl pair.1], pair.2, rfl⟩
      · obtain ⟨initial, negative, hword⟩ := ih hrest
        refine ⟨[Sum.inl pair.1, Sum.inr pair.2] ++ initial,
          negative, ?_⟩
        rw [show positiveNegativeWord (pair :: pairs) =
          [Sum.inl pair.1, Sum.inr pair.2] ++
            positiveNegativeWord pairs by rfl, hword,
          List.append_assoc]

/-- A nonempty negative-positive pair word starts negatively. -/
theorem negativePositiveWord_starts
    {Positive : Type uP} {Negative : Type uN}
    {pairs : List (Negative × Positive)} (hpairs : pairs ≠ []) :
    ∃ (negative : Negative) (tail : List (Positive ⊕ Negative)),
      negativePositiveWord pairs = Sum.inr negative :: tail := by
  obtain ⟨pair, pairs, rfl⟩ := List.exists_cons_of_ne_nil hpairs
  exact ⟨pair.1, Sum.inl pair.2 :: negativePositiveWord pairs, rfl⟩

/-- A nonempty negative-positive pair word ends positively. -/
theorem negativePositiveWord_ends
    {Positive : Type uP} {Negative : Type uN}
    {pairs : List (Negative × Positive)} (hpairs : pairs ≠ []) :
    ∃ (initial : List (Positive ⊕ Negative)) (positive : Positive),
      negativePositiveWord pairs = initial ++ [Sum.inl positive] := by
  induction pairs with
  | nil => exact False.elim (hpairs rfl)
  | cons pair pairs ih =>
      by_cases hrest : pairs = []
      · subst pairs
        exact ⟨[Sum.inr pair.1], pair.2, rfl⟩
      · obtain ⟨initial, positive, hword⟩ := ih hrest
        refine ⟨[Sum.inr pair.1, Sum.inl pair.2] ++ initial,
          positive, ?_⟩
        rw [show negativePositiveWord (pair :: pairs) =
          [Sum.inr pair.1, Sum.inl pair.2] ++
            negativePositiveWord pairs by rfl, hword,
          List.append_assoc]

/-- A nonempty pair word is a balanced positive-to-negative block. -/
theorem positiveNegativeWord_isBlock
    {Positive : Type uP} {Negative : Type uN}
    {pairs : List (Positive × Negative)} (hpairs : pairs ≠ []) :
    IsPositiveNegativeBlock (positiveNegativeWord pairs) := by
  refine ⟨positiveNegativeWord_isChain pairs, ?_, ?_⟩
  · exact positiveNegativeWord_starts hpairs
  · exact positiveNegativeWord_ends hpairs

/-- Adding one final positive endpoint makes a positive-heavy block. -/
theorem positiveHeavyWord_isBlock
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Positive × Negative)) (last : Positive) :
    IsPositiveHeavyBlock
      (positiveNegativeWord pairs ++ [Sum.inl last]) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (positiveNegativeWord_isChain pairs).append
      (List.isChain_singleton (Sum.inl last))
    intro previous hprevious _next _hnext
    by_cases hpairs : pairs = []
    · subst pairs
      simp [positiveNegativeWord] at hprevious
    · obtain ⟨initial, negative, hword⟩ :=
        positiveNegativeWord_ends hpairs
      have hpreviousEq : previous = Sum.inr negative := by
        simpa [hword] using hprevious.symm
      subst previous
      simp at _hnext
      subst _next
      trivial
  · by_cases hpairs : pairs = []
    · subst pairs
      exact ⟨last, [], rfl⟩
    · obtain ⟨positive, tail, hword⟩ :=
        positiveNegativeWord_starts hpairs
      exact ⟨positive, tail ++ [Sum.inl last], by
        rw [hword, List.cons_append]⟩
  · exact ⟨positiveNegativeWord pairs, last, rfl⟩

/-- Adding one final negative endpoint makes a negative-heavy block. -/
theorem negativeHeavyWord_isBlock
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) (last : Negative) :
    IsNegativeHeavyBlock
      (negativePositiveWord pairs ++ [Sum.inr last]) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (negativePositiveWord_isChain pairs).append
      (List.isChain_singleton (Sum.inr last))
    intro previous hprevious _next _hnext
    by_cases hpairs : pairs = []
    · subst pairs
      simp [negativePositiveWord] at hprevious
    · obtain ⟨initial, positive, hword⟩ :=
        negativePositiveWord_ends hpairs
      have hpreviousEq : previous = Sum.inl positive := by
        simpa [hword] using hprevious.symm
      subst previous
      simp at _hnext
      subst _next
      trivial
  · by_cases hpairs : pairs = []
    · subst pairs
      exact ⟨last, [], rfl⟩
    · obtain ⟨negative, tail, hword⟩ :=
        negativePositiveWord_starts hpairs
      exact ⟨negative, tail ++ [Sum.inr last], by
        rw [hword, List.cons_append]⟩
  · exact ⟨negativePositiveWord pairs, last, rfl⟩

/-- Reversing a negative-positive word gives a positive-negative word. -/
theorem reverse_negativePositiveWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) :
    (negativePositiveWord pairs).reverse =
      positiveNegativeWord
        (pairs.reverse.map fun pair => (pair.2, pair.1)) := by
  induction pairs with
  | nil => rfl
  | cons pair pairs ih =>
      rw [show negativePositiveWord (pair :: pairs) =
        [Sum.inr pair.1, Sum.inl pair.2] ++
          negativePositiveWord pairs by rfl]
      simp [ih, positiveNegativeWord]

/-- The three possible endpoint imbalances of a nonempty alternating path. -/
inductive AlternatingComponentShape
    {Positive : Type uP} {Negative : Type uN} :
    (order : List (Positive ⊕ Negative)) → Prop
  | balanced
      {order : List (Positive ⊕ Negative)}
      (pairs : List (Positive × Negative))
      (nonempty : pairs ≠ [])
      (word : order = positiveNegativeWord pairs) :
      AlternatingComponentShape order
  | positiveHeavy
      {order : List (Positive ⊕ Negative)}
      (pairs : List (Positive × Negative)) (last : Positive)
      (word : order = positiveNegativeWord pairs ++ [Sum.inl last]) :
      AlternatingComponentShape order
  | negativeHeavy
      {order : List (Positive ⊕ Negative)}
      (pairs : List (Negative × Positive)) (last : Negative)
      (word : order = negativePositiveWord pairs ++ [Sum.inr last]) :
      AlternatingComponentShape order

/-- Reversal preserves the negative-heavy form of an alternating word. -/
theorem reverse_negativeHeavyWord
    {Positive : Type uP} {Negative : Type uN}
    (pairs : List (Negative × Positive)) (last : Negative) :
    ∃ (reversedPairs : List (Negative × Positive))
        (reversedLast : Negative),
      (negativePositiveWord pairs ++ [Sum.inr last]).reverse =
        negativePositiveWord reversedPairs ++ [Sum.inr reversedLast] := by
  induction pairs generalizing last with
  | nil =>
      exact ⟨[], last, rfl⟩
  | cons pair pairs ih =>
      obtain ⟨reversedPairs, reversedLast, hword⟩ := ih last
      refine ⟨reversedPairs ++ [(reversedLast, pair.2)], pair.1, ?_⟩
      rw [show negativePositiveWord (pair :: pairs) =
        [Sum.inr pair.1, Sum.inl pair.2] ++
          negativePositiveWord pairs by rfl]
      rw [List.append_assoc, List.reverse_append, hword]
      simp [negativePositiveWord]

/-- A path order for one connected component, mapped to original vertices. -/
structure ComponentPathLayout
    {Positive : Type uP} {Negative : Type uN}
    (G : SimpleGraph (Positive ⊕ Negative))
    (component : G.ConnectedComponent) where
  order : List (Positive ⊕ Negative)
  nodup : order.Nodup
  mem_iff : ∀ vertex, vertex ∈ order ↔ vertex ∈ component.supp
  chain : order.IsChain G.Adj
  covers :
    ∀ {left right}, G.Adj left right → left ∈ component.supp →
      [left, right] <:+: order ∨ [right, left] <:+: order

namespace ComponentPathLayout

variable
    {Positive : Type uP} {Negative : Type uN}
    {G : SimpleGraph (Positive ⊕ Negative)}
    {component : G.ConnectedComponent}

theorem order_ne_nil
    (layout : ComponentPathLayout G component) : layout.order ≠ [] := by
  intro hempty
  obtain ⟨vertex, hvertex⟩ := component.nonempty_supp
  have := (layout.mem_iff vertex).mpr hvertex
  simpa [hempty] using this

/-- Reorient one connected-component path. -/
def reverse (layout : ComponentPathLayout G component) :
    ComponentPathLayout G component where
  order := layout.order.reverse
  nodup := List.nodup_reverse.mpr layout.nodup
  mem_iff vertex := by simpa using layout.mem_iff vertex
  chain := by
    rw [List.isChain_reverse]
    exact layout.chain.imp fun _ _ hadj => hadj.symm
  covers := by
    intro left right hadj hleft
    rcases layout.covers hadj hleft with hforward | hbackward
    · rcases hforward with ⟨before, after, horder⟩
      right
      refine ⟨after.reverse, before.reverse, ?_⟩
      rw [← horder]
      simp
    · rcases hbackward with ⟨before, after, horder⟩
      left
      refine ⟨after.reverse, before.reverse, ?_⟩
      rw [← horder]
      simp

end ComponentPathLayout

/-- Build the Hamilton path of one component of a bipartite linear forest. -/
noncomputable def componentPathLayout
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic)
    (hdegree : ∀ vertex, G.degree vertex ≤ 2)
    (component : G.ConnectedComponent) :
    ComponentPathLayout G component := by
  classical
  have hcomponentDegree :
      ∀ vertex, component.toSimpleGraph.degree vertex ≤ 2 := by
    intro vertex
    rw [← component.toSimpleGraph.card_neighborSet_eq_degree]
    calc
      Fintype.card (component.toSimpleGraph.neighborSet vertex) ≤
          Fintype.card (G.neighborSet vertex.1) := by
        apply Fintype.card_le_of_injective
          (fun neighbor : component.toSimpleGraph.neighborSet vertex =>
            (⟨neighbor.1.1, neighbor.2⟩ : G.neighborSet vertex.1))
        intro left right heq
        have hval : left.1.1 = right.1.1 :=
          congrArg (fun x : G.neighborSet vertex.1 => x.1) heq
        exact Subtype.ext (Subtype.ext hval)
      _ = G.degree vertex.1 := G.card_neighborSet_eq_degree vertex.1
      _ ≤ 2 := hdegree vertex.1
  let path : SpanningPathOrder component.toSimpleGraph :=
    Classical.choice
      (exists_spanningPathOrder_of_isTree_degree_le_two
        component.toSimpleGraph
        (hacyclic.isTree_connectedComponent component)
        hcomponentDegree)
  let order := path.order.map (fun vertex : component.supp => vertex.1)
  refine {
    order := order
    nodup := ?_
    mem_iff := ?_
    chain := ?_
    covers := ?_
  }
  · exact path.nodup.map (fun _ _ heq => Subtype.ext heq)
  · intro vertex
    constructor
    · intro hmem
      obtain ⟨other, _hother, heq⟩ :=
        List.mem_map.mp (show vertex ∈ order from hmem)
      simpa [← heq] using other.2
    · intro hmem
      exact List.mem_map.mpr
        ⟨(⟨vertex, hmem⟩ : component.supp),
          path.complete ⟨vertex, hmem⟩, rfl⟩
  · change List.IsChain G.Adj
      (path.order.map (fun vertex : component.supp => vertex.1))
    rw [List.isChain_map]
    simpa [SimpleGraph.ConnectedComponent.toSimpleGraph] using path.chain
  · intro left right hadj hleft
    have hright : right ∈ component.supp :=
      (component.mem_supp_congr_adj hadj).mp hleft
    let componentLeft : component.supp := ⟨left, hleft⟩
    let componentRight : component.supp := ⟨right, hright⟩
    have hcomponentAdj :
        component.toSimpleGraph.Adj componentLeft componentRight := hadj
    rcases path.covers hcomponentAdj with hforward | hbackward
    · left
      simpa [order, componentLeft, componentRight] using
        hforward.map (fun vertex : component.supp => vertex.1)
    · right
      simpa [order, componentLeft, componentRight] using
        hbackward.map (fun vertex : component.supp => vertex.1)

/-- One component path together with its oriented imbalance shape. -/
structure OrientedComponentLayout
    {Positive : Type uP} {Negative : Type uN}
    (G : SimpleGraph (Positive ⊕ Negative))
    (component : G.ConnectedComponent)
    extends ComponentPathLayout G component where
  shape : AlternatingComponentShape toComponentPathLayout.order

/-- Orient and classify one connected component of a bipartite linear forest. -/
noncomputable def orientedComponentLayout
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic)
    (hdegree : ∀ vertex, G.degree vertex ≤ 2)
    (hcross : ∀ {left right}, G.Adj left right → OppositeSign left right)
    (component : G.ConnectedComponent) :
    OrientedComponentLayout G component := by
  classical
  let layout := componentPathLayout G hacyclic hdegree component
  have hne := layout.order_ne_nil
  let first := layout.order.head hne
  let tail := layout.order.tail
  have horder : layout.order = first :: tail := by
    exact (List.cons_head_tail hne).symm
  have hopposite : List.IsChain OppositeSign (first :: tail) := by
    rw [← horder]
    exact layout.chain.imp fun _ _ hadj => hcross hadj
  cases hfirst : first with
  | inl positive =>
      have horder' : layout.order = Sum.inl positive :: tail := by
        simpa [hfirst] using horder
      have hopposite' :
          List.IsChain OppositeSign (Sum.inl positive :: tail) := by
        simpa [hfirst] using hopposite
      have hshape : AlternatingComponentShape layout.order := by
        rcases oppositeSign_chain_from_positive_decompose
            positive tail hopposite' with hbalanced | hheavy
        · obtain ⟨pairs, hpairs, hword⟩ := hbalanced
          exact .balanced pairs hpairs (horder'.trans hword)
        · obtain ⟨pairs, last, hword⟩ := hheavy
          exact .positiveHeavy pairs last (horder'.trans hword)
      exact {
        toComponentPathLayout := layout
        shape := hshape
      }
  | inr negative =>
      have horder' : layout.order = Sum.inr negative :: tail := by
        simpa [hfirst] using horder
      have hopposite' :
          List.IsChain OppositeSign (Sum.inr negative :: tail) := by
        simpa [hfirst] using hopposite
      let reversed := layout.reverse
      have hshape : AlternatingComponentShape reversed.order := by
        rcases oppositeSign_chain_from_negative_decompose
            negative tail hopposite' with hbalanced | hheavy
        · obtain ⟨pairs, hpairs, hword⟩ := hbalanced
          apply AlternatingComponentShape.balanced
            (pairs.reverse.map fun pair => (pair.2, pair.1))
          · intro hempty
            have : pairs.reverse = [] := by
              simpa using hempty
            exact hpairs (by
              have := congrArg List.reverse this
              simpa using this)
          · change layout.order.reverse =
              positiveNegativeWord
                (pairs.reverse.map fun pair => (pair.2, pair.1))
            rw [horder', hword, reverse_negativePositiveWord]
        · obtain ⟨pairs, last, hword⟩ := hheavy
          obtain ⟨reversedPairs, reversedLast, hreverseWord⟩ :=
            reverse_negativeHeavyWord pairs last
          apply AlternatingComponentShape.negativeHeavy
            reversedPairs reversedLast
          change layout.order.reverse =
            negativePositiveWord reversedPairs ++ [Sum.inr reversedLast]
          rw [horder', hword, hreverseWord]
      exact {
        toComponentPathLayout := reversed
        shape := hshape
      }

namespace OrientedComponentLayout

variable
    {Positive : Type uP} {Negative : Type uN}
    {G : SimpleGraph (Positive ⊕ Negative)}
    {component : G.ConnectedComponent}

/-- The signed mass of an oriented component order. -/
def mass (layout : OrientedComponentLayout G component) : ℤ :=
  (layout.order.map sideWeight).sum

/-- In particular, every component mass is one of the three possible values. -/
theorem mass_cases (layout : OrientedComponentLayout G component) :
    layout.mass = 0 ∨ layout.mass = 1 ∨ layout.mass = -1 := by
  cases layout.shape with
  | balanced pairs hpairs hword =>
      exact Or.inl (by simp [mass, hword])
  | positiveHeavy pairs last hword =>
      exact Or.inr (Or.inl (by simp [mass, hword, sideWeight]))
  | negativeHeavy pairs last hword =>
      exact Or.inr (Or.inr (by simp [mass, hword, sideWeight]))

/-- A zero-mass component is one balanced positive-to-negative block. -/
theorem isPositiveNegativeBlock_of_mass_eq_zero
    (layout : OrientedComponentLayout G component)
    (hmass : layout.mass = 0) :
    IsPositiveNegativeBlock layout.order := by
  cases layout.shape with
  | balanced pairs hpairs hword =>
      rw [hword]
      exact positiveNegativeWord_isBlock hpairs
  | positiveHeavy pairs last hword =>
      have hpositive : layout.mass = 1 := by
        simp [mass, hword, sideWeight]
      omega
  | negativeHeavy pairs last hword =>
      have hnegative : layout.mass = -1 := by
        simp [mass, hword, sideWeight]
      omega

/-- A mass-one component is positive-heavy. -/
theorem isPositiveHeavyBlock_of_mass_eq_one
    (layout : OrientedComponentLayout G component)
    (hmass : layout.mass = 1) :
    IsPositiveHeavyBlock layout.order := by
  cases layout.shape with
  | balanced pairs hpairs hword =>
      have hzero : layout.mass = 0 := by simp [mass, hword]
      omega
  | positiveHeavy pairs last hword =>
      rw [hword]
      exact positiveHeavyWord_isBlock pairs last
  | negativeHeavy pairs last hword =>
      have hnegative : layout.mass = -1 := by
        simp [mass, hword, sideWeight]
      omega

/-- A mass-minus-one component is negative-heavy. -/
theorem isNegativeHeavyBlock_of_mass_eq_neg_one
    (layout : OrientedComponentLayout G component)
    (hmass : layout.mass = -1) :
    IsNegativeHeavyBlock layout.order := by
  cases layout.shape with
  | balanced pairs hpairs hword =>
      have hzero : layout.mass = 0 := by simp [mass, hword]
      omega
  | positiveHeavy pairs last hword =>
      have hpositive : layout.mass = 1 := by
        simp [mass, hword, sideWeight]
      omega
  | negativeHeavy pairs last hword =>
      rw [hword]
      exact negativeHeavyWord_isBlock pairs last

/-- Mass of the path order equals mass summed directly over its component. -/
theorem mass_eq_component_sum
    [Fintype Positive] [Fintype Negative]
    [DecidableEq Positive] [DecidableEq Negative]
    [DecidableRel G.Adj]
    (layout : OrientedComponentLayout G component) :
    layout.mass = ∑ vertex : component.supp, sideWeight vertex.1 := by
  classical
  have hfinset : layout.order.toFinset = component.supp.toFinset := by
    ext vertex
    simp only [List.mem_toFinset, Set.mem_toFinset]
    exact layout.mem_iff vertex
  calc
    layout.mass = layout.order.toFinset.sum sideWeight := by
      exact (List.sum_toFinset sideWeight layout.nodup).symm
    _ = component.supp.toFinset.sum sideWeight := by rw [hfinset]
    _ = ∑ vertex : component.supp, sideWeight vertex.1 := by
      exact Finset.sum_subtype component.supp.toFinset
        (fun vertex => by simp) sideWeight

end OrientedComponentLayout

/-- The supports of connected components form a sigma-type copy of all vertices. -/
def connectedComponentSigmaEquiv
    {Vertex : Type*} (G : SimpleGraph Vertex) :
    (Σ component : G.ConnectedComponent, component.supp) ≃ Vertex where
  toFun vertex := vertex.2.1
  invFun vertex :=
    ⟨G.connectedComponentMk vertex,
      ⟨vertex, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩⟩
  left_inv vertex := by
    rcases vertex with ⟨component, ⟨vertex, hvertex⟩⟩
    have hcomponent : G.connectedComponentMk vertex = component := hvertex
    subst component
    rfl
  right_inv vertex := rfl

/-- Summing oriented-component masses is the signed mass of all vertices. -/
theorem sum_orientedComponent_mass_eq
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    [DecidableEq Positive] [DecidableEq Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (layouts : ∀ component, OrientedComponentLayout G component) :
    (∑ component, (layouts component).mass) =
      ∑ vertex : Positive ⊕ Negative, sideWeight vertex := by
  classical
  calc
    (∑ component, (layouts component).mass) =
        ∑ component : G.ConnectedComponent,
          ∑ vertex : SimpleGraph.ConnectedComponent.supp component,
          sideWeight vertex.1 := by
      apply Finset.sum_congr rfl
      intro component _
      exact (layouts component).mass_eq_component_sum
    _ = ∑ vertex :
          (Σ component : G.ConnectedComponent, component.supp),
          sideWeight vertex.2.1 := by
      exact (Fintype.sum_sigma'
        (fun (component : G.ConnectedComponent)
          (vertex : component.supp) => sideWeight vertex.1)).symm
    _ = ∑ vertex : Positive ⊕ Negative, sideWeight vertex := by
      exact (connectedComponentSigmaEquiv G).sum_comp sideWeight

/-- Equal bipartition sizes force total oriented-component mass to vanish. -/
theorem sum_orientedComponent_mass_eq_zero
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    [DecidableEq Positive] [DecidableEq Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (layouts : ∀ component, OrientedComponentLayout G component)
    (hcard : Fintype.card Positive = Fintype.card Negative) :
    (∑ component, (layouts component).mass) = 0 := by
  rw [sum_orientedComponent_mass_eq G layouts]
  simp [sideWeight, hcard]

/-- Zero total mass pairs the positive-heavy and negative-heavy components. -/
theorem positiveHeavy_card_eq_negativeHeavy
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    [DecidableEq Positive] [DecidableEq Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (layouts : ∀ component, OrientedComponentLayout G component)
    (hzero : (∑ component, (layouts component).mass) = 0) :
    (Finset.univ.filter
        fun component => (layouts component).mass = 1).card =
      (Finset.univ.filter
        fun component => (layouts component).mass = -1).card := by
  classical
  let componentMass : G.ConnectedComponent → ℤ :=
    fun component => (layouts component).mass
  have hcases :
      ∀ component, componentMass component = 0 ∨
        componentMass component = 1 ∨ componentMass component = -1 :=
    fun component => (layouts component).mass_cases
  have hform : ∀ component, componentMass component =
      (if componentMass component = 1 then 1
        else if componentMass component = -1 then -1 else 0) := by
    intro component
    rcases hcases component with hzero | hone | hnegative
    · simp [hzero]
    · simp [hone]
    · simp [hnegative]
  have hsumForm : (∑ component, componentMass component) =
      ∑ component,
        (if componentMass component = 1 then 1
          else if componentMass component = -1 then -1 else 0) := by
    apply Finset.sum_congr rfl
    intro component _
    exact hform component
  have hsum : (∑ component, componentMass component) = 0 := by
    simpa [componentMass] using hzero
  rw [hsumForm] at hsum
  change (Finset.univ.sum fun component =>
    if componentMass component = 1 then 1
    else if componentMass component = -1 then -1 else 0) = 0 at hsum
  rw [Finset.sum_ite, Finset.sum_ite] at hsum
  have hfilter :
      (Finset.univ.filter
          fun component => ¬componentMass component = 1).filter
            (fun component => componentMass component = -1) =
        Finset.univ.filter
          (fun component => componentMass component = -1) := by
    ext component
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  simp only [Finset.sum_const, nsmul_eq_mul,
    mul_one, mul_neg, mul_zero] at hsum
  rw [hfilter] at hsum
  simpa [componentMass] using (show
    (Finset.univ.filter
        fun component => componentMass component = 1).card =
      (Finset.univ.filter
        fun component => componentMass component = -1).card by omega)

/--
A complete alternating vertex order of a bipartite linear forest.  Every
forest edge occurs as one adjacent pair in the order.
-/
structure BipartiteLinearForestAlternatingLayout
    {Positive : Type uP} {Negative : Type uN}
    (G : SimpleGraph (Positive ⊕ Negative)) where
  order : List (Positive ⊕ Negative)
  nodup : order.Nodup
  complete : ∀ vertex, vertex ∈ order
  alternating : order.IsChain OppositeSign
  covers :
    ∀ {left right}, G.Adj left right →
      [left, right] <:+: order ∨ [right, left] <:+: order

/--
Every finite bipartite linear forest with equally many vertices on its two
sides has a complete sign-alternating order in which all forest edges are
adjacent.  The proof is componentwise and pairs the two kinds of odd path.
-/
theorem exists_bipartiteLinearForestAlternatingLayout
    {Positive : Type uP} {Negative : Type uN}
    [Fintype Positive] [Fintype Negative]
    [DecidableEq Positive] [DecidableEq Negative]
    (G : SimpleGraph (Positive ⊕ Negative)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic)
    (hdegree : ∀ vertex, G.degree vertex ≤ 2)
    (hcross : ∀ {left right}, G.Adj left right → OppositeSign left right)
    (hcard : Fintype.card Positive = Fintype.card Negative) :
    Nonempty (BipartiteLinearForestAlternatingLayout G) := by
  classical
  let layouts : ∀ component : G.ConnectedComponent,
      OrientedComponentLayout G component :=
    fun component =>
      orientedComponentLayout G hacyclic hdegree hcross component
  let BalancedComponent :=
    {component : G.ConnectedComponent // (layouts component).mass = 0}
  let PositiveHeavyComponent :=
    {component : G.ConnectedComponent // (layouts component).mass = 1}
  let NegativeHeavyComponent :=
    {component : G.ConnectedComponent // (layouts component).mass = -1}
  have hzero := sum_orientedComponent_mass_eq_zero G layouts hcard
  have hheavyFilterCard :=
    positiveHeavy_card_eq_negativeHeavy G layouts hzero
  have hheavyCard :
      Fintype.card PositiveHeavyComponent =
        Fintype.card NegativeHeavyComponent := by
    simpa [PositiveHeavyComponent, NegativeHeavyComponent,
      Fintype.card_subtype] using hheavyFilterCard
  let heavyEquiv : PositiveHeavyComponent ≃ NegativeHeavyComponent :=
    Fintype.equivOfCardEq hheavyCard
  let balancedList : List BalancedComponent := Finset.univ.toList
  let positiveList : List PositiveHeavyComponent := Finset.univ.toList
  let balancedValues : List G.ConnectedComponent :=
    balancedList.map fun component => component.1
  let positiveValues : List G.ConnectedComponent :=
    positiveList.map fun component => component.1
  let negativeValues : List G.ConnectedComponent :=
    positiveList.map fun component => (heavyEquiv component).1
  let heavySequence : List G.ConnectedComponent :=
    positiveList.flatMap fun component =>
      [component.1, (heavyEquiv component).1]
  let componentSequence : List G.ConnectedComponent :=
    balancedValues ++ heavySequence
  have hbalancedNodup : balancedValues.Nodup := by
    exact (Finset.nodup_toList _).map
      (fun _ _ heq => Subtype.ext heq)
  have hpositiveNodup : positiveValues.Nodup := by
    exact (Finset.nodup_toList _).map
      (fun _ _ heq => Subtype.ext heq)
  have hnegativeNodup : negativeValues.Nodup := by
    exact (Finset.nodup_toList _).map (fun left right heq => by
      apply heavyEquiv.injective
      exact Subtype.ext heq)
  have hbalancedPositive :
      List.Disjoint balancedValues positiveValues := by
    rw [List.disjoint_left]
    intro component hbalanced hpositive
    obtain ⟨balanced, _hbalancedMem, hbalancedEq⟩ :=
      List.mem_map.mp hbalanced
    obtain ⟨positive, _hpositiveMem, hpositiveEq⟩ :=
      List.mem_map.mp hpositive
    have hzeroMass : (layouts component).mass = 0 := by
      rw [← hbalancedEq]
      exact balanced.2
    have honeMass : (layouts component).mass = 1 := by
      rw [← hpositiveEq]
      exact positive.2
    omega
  have hbalancedNegative :
      List.Disjoint balancedValues negativeValues := by
    rw [List.disjoint_left]
    intro component hbalanced hnegative
    obtain ⟨balanced, _hbalancedMem, hbalancedEq⟩ :=
      List.mem_map.mp hbalanced
    obtain ⟨positive, _hpositiveMem, hnegativeEq⟩ :=
      List.mem_map.mp hnegative
    have hzeroMass : (layouts component).mass = 0 := by
      rw [← hbalancedEq]
      exact balanced.2
    have hnegativeMass : (layouts component).mass = -1 := by
      rw [← hnegativeEq]
      exact (heavyEquiv positive).2
    omega
  have hpositiveNegative :
      List.Disjoint positiveValues negativeValues := by
    rw [List.disjoint_left]
    intro component hpositive hnegative
    obtain ⟨positive, _hpositiveMem, hpositiveEq⟩ :=
      List.mem_map.mp hpositive
    obtain ⟨other, _hotherMem, hnegativeEq⟩ :=
      List.mem_map.mp hnegative
    have honeMass : (layouts component).mass = 1 := by
      rw [← hpositiveEq]
      exact positive.2
    have hnegativeMass : (layouts component).mass = -1 := by
      rw [← hnegativeEq]
      exact (heavyEquiv other).2
    omega
  have hseparatedNodup :
      (balancedValues ++ positiveValues ++ negativeValues).Nodup := by
    apply List.Nodup.append
      (List.Nodup.append hbalancedNodup hpositiveNodup
        hbalancedPositive)
      hnegativeNodup
    rw [List.disjoint_left]
    intro component hleft hnegative
    rw [List.mem_append] at hleft
    exact hleft.elim
      (fun hbalanced => hbalancedNegative hbalanced hnegative)
      (fun hpositive => hpositiveNegative hpositive hnegative)
  have hheavyPerm :
      heavySequence.Perm (positiveValues ++ negativeValues) := by
    have hperm :=
      (List.flatMap_append_perm positiveList
        (fun component => [component.1])
        (fun component => [(heavyEquiv component).1])).symm
    simpa [heavySequence, positiveValues, negativeValues,
      ← List.map_eq_flatMap] using hperm
  have hsequencePerm :
      componentSequence.Perm
        (balancedValues ++ positiveValues ++ negativeValues) := by
    simpa [List.append_assoc] using
      hheavyPerm.append_left balancedValues
  have hsequenceNodup : componentSequence.Nodup :=
    hsequencePerm.nodup_iff.mpr hseparatedNodup
  have hsequenceComplete :
      ∀ component : G.ConnectedComponent,
        component ∈ componentSequence := by
    intro component
    rcases (layouts component).mass_cases with hmass | hmass | hmass
    · apply List.mem_append_left
      exact List.mem_map.mpr
        ⟨(⟨component, hmass⟩ : BalancedComponent), by
          simp [balancedList], rfl⟩
    · apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨(⟨component, hmass⟩ : PositiveHeavyComponent), ?_, ?_⟩
      · simp [positiveList]
      · simp
    · let negative : NegativeHeavyComponent := ⟨component, hmass⟩
      let positive : PositiveHeavyComponent := heavyEquiv.symm negative
      apply List.mem_append_right
      apply List.mem_flatMap.mpr
      refine ⟨positive, by simp [positiveList], ?_⟩
      right
      exact List.mem_singleton.mpr (by
        change component = (heavyEquiv positive).1
        simp [positive, negative])
  let order : List (Positive ⊕ Negative) :=
    componentSequence.flatMap fun component => (layouts component).order
  have hcomponentOrdersDisjoint :
      List.Pairwise
        (Function.onFun List.Disjoint
          (fun component => (layouts component).order))
        componentSequence := by
    apply hsequenceNodup.imp
    intro left right hne
    change List.Disjoint (layouts left).order (layouts right).order
    rw [List.disjoint_left]
    intro vertex hleft hright
    have hleftSupp := ((layouts left).mem_iff vertex).mp hleft
    have hrightSupp := ((layouts right).mem_iff vertex).mp hright
    exact (Set.disjoint_left.mp
      (SimpleGraph.pairwise_disjoint_supp_connectedComponent G hne))
        hleftSupp hrightSupp
  have horderNodup : order.Nodup := by
    apply List.nodup_flatMap.mpr
    exact ⟨fun component _ => (layouts component).nodup,
      hcomponentOrdersDisjoint⟩
  have horderComplete : ∀ vertex, vertex ∈ order := by
    intro vertex
    let component := G.connectedComponentMk vertex
    apply List.mem_flatMap.mpr
    exact ⟨component, hsequenceComplete component,
      ((layouts component).mem_iff vertex).mpr rfl⟩
  let balancedBlocks : List (List (Positive ⊕ Negative)) :=
    balancedList.map fun component => (layouts component.1).order
  let heavyBlocks : List (List (Positive ⊕ Negative)) :=
    positiveList.map fun component =>
      (layouts component.1).order ++
        (layouts (heavyEquiv component).1).order
  let blocks : List (List (Positive ⊕ Negative)) :=
    balancedBlocks ++ heavyBlocks
  have hblocks :
      ∀ block ∈ blocks, IsPositiveNegativeBlock block := by
    intro block hblock
    rw [List.mem_append] at hblock
    rcases hblock with hbalanced | hheavy
    · obtain ⟨component, _hcomponent, rfl⟩ :=
        List.mem_map.mp hbalanced
      exact (layouts component.1).isPositiveNegativeBlock_of_mass_eq_zero
        component.2
    · obtain ⟨component, _hcomponent, rfl⟩ :=
        List.mem_map.mp hheavy
      exact
        ((layouts component.1).isPositiveHeavyBlock_of_mass_eq_one
          component.2).append_negativeHeavy
            ((layouts (heavyEquiv component).1
              ).isNegativeHeavyBlock_of_mass_eq_neg_one
                (heavyEquiv component).2)
  have hblocksOrder : blocks.flatten = order := by
    simp [blocks, balancedBlocks, heavyBlocks, order,
      componentSequence, balancedValues, heavySequence,
      List.flatten_eq_flatMap, List.flatMap_append,
      List.flatMap_map, List.flatMap_assoc]
  have horderAlternating : order.IsChain OppositeSign := by
    rw [← hblocksOrder]
    exact isChain_flatten_positiveNegativeBlocks blocks hblocks
  have hcomponentOrderInfix :
      ∀ component : G.ConnectedComponent,
        (layouts component).order <:+: order := by
    intro component
    obtain ⟨before, after, hsequence⟩ :=
      List.mem_iff_append.mp (hsequenceComplete component)
    refine ⟨before.flatMap (fun other => (layouts other).order),
      after.flatMap (fun other => (layouts other).order), ?_⟩
    change
      before.flatMap (fun other => (layouts other).order) ++
          (layouts component).order ++
            after.flatMap (fun other => (layouts other).order) = order
    simp [order, hsequence, List.flatMap_append, List.append_assoc]
  refine ⟨{
    order := order
    nodup := horderNodup
    complete := horderComplete
    alternating := horderAlternating
    covers := ?_
  }⟩
  intro left right hadj
  let component := G.connectedComponentMk left
  have hleft : left ∈ component.supp := rfl
  rcases (layouts component).covers hadj hleft with
    hforward | hbackward
  · exact Or.inl (hforward.trans (hcomponentOrderInfix component))
  · exact Or.inr (hbackward.trans (hcomponentOrderInfix component))


end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Data.List.Chain

/-!
# Linear orders covering finite path forests

The central structural fact is proved by leaf deletion: every finite tree of
maximum degree two has a Hamilton path, and that path contains every edge of
the tree.  This is the graph-theoretic layer behind selected-block occurrence
layouts; no bounded search or graph census enters the proof.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uV

noncomputable section

/-- A duplicate-free vertex order which is a path and contains every vertex. -/
structure SpanningPathOrder
    {V : Type uV} (G : SimpleGraph V) where
  /-- The vertices in path order. -/
  order : List V
  /-- No vertex occurs twice. -/
  nodup : order.Nodup
  /-- Every vertex occurs. -/
  complete : ∀ vertex : V, vertex ∈ order
  /-- Consecutive vertices are graph-adjacent. -/
  chain : order.IsChain G.Adj
  /-- Every graph edge occurs as a consecutive pair, in one orientation. -/
  covers :
    ∀ {left right}, G.Adj left right →
      [left, right] <:+: order ∨ [right, left] <:+: order

namespace SpanningPathOrder

variable {V : Type uV} {G : SimpleGraph V}

/-- A spanning path order is nonempty whenever its vertex type is nonempty. -/
theorem order_ne_nil [Nonempty V] (path : SpanningPathOrder G) :
    path.order ≠ [] := by
  intro hempty
  have := path.complete (Classical.choice inferInstance)
  simpa [hempty] using this

/-- Reversing a spanning path order gives another spanning path order. -/
def reverse (path : SpanningPathOrder G) : SpanningPathOrder G where
  order := path.order.reverse
  nodup := List.nodup_reverse.mpr path.nodup
  complete vertex := by simpa using path.complete vertex
  chain := by
    rw [List.isChain_reverse]
    exact path.chain.imp fun _ _ hadj => hadj.symm
  covers := by
    intro left right hadj
    rcases path.covers hadj with hforward | hbackward
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

end SpanningPathOrder

/--
In a duplicate-free graph path, a vertex of graph degree at most one must be
one of the two endpoints.
-/
theorem spanningPath_endpoint_of_degree_le_one
    {V : Type uV} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (path : SpanningPathOrder G) (vertex : V)
    (hdegree : G.degree vertex ≤ 1) :
    (∃ tail, path.order = vertex :: tail) ∨
      ∃ initial, path.order = initial ++ [vertex] := by
  obtain ⟨left, right, hsplit⟩ :=
    List.mem_iff_append.mp (path.complete vertex)
  by_cases hleft : left = []
  · subst left
    exact Or.inl ⟨right, by simpa using hsplit⟩
  by_cases hright : right = []
  · subst right
    exact Or.inr ⟨left, by simpa using hsplit⟩
  exfalso
  let previous := left.getLast hleft
  obtain ⟨next, tail, hrightEq⟩ := List.exists_cons_of_ne_nil hright
  subst right
  have hleftEq : left = left.dropLast ++ [previous] := by
    exact (List.dropLast_append_getLast hleft).symm
  have hchain :
      List.IsChain G.Adj
        (left.dropLast ++ previous :: vertex :: next :: tail) := by
    have hpathChain :
        List.IsChain G.Adj (left ++ vertex :: next :: tail) := by
      rw [← hsplit]
      exact path.chain
    rw [hleftEq] at hpathChain
    simpa only [List.append_assoc, List.cons_append] using hpathChain
  have hpreviousAdj : G.Adj previous vertex := by
    exact (List.isChain_append_cons_cons.mp hchain).2.1
  have hnextAdj : G.Adj vertex next := by
    exact (List.isChain_append_cons_cons.mp hchain).2.2.rel
  have hpreviousNeNext : previous ≠ next := by
    intro heq
    subst next
    have hnodup :
        (left.dropLast ++ previous :: vertex :: previous :: tail).Nodup := by
      have hpathNodup :
          (left ++ vertex :: previous :: tail).Nodup := by
        rw [← hsplit]
        exact path.nodup
      rw [hleftEq] at hpathNodup
      simpa only [List.append_assoc, List.cons_append] using hpathNodup
    have hsuffix := (List.nodup_append.mp hnodup).2.1
    exact (List.nodup_cons.mp hsuffix).1 (by simp)
  have hpairSubset : ({previous, next} : Finset V) ⊆ G.neighborFinset vertex := by
    intro other hother
    simp only [Finset.mem_insert, Finset.mem_singleton] at hother
    rcases hother with rfl | rfl
    · simpa using hpreviousAdj.symm
    · simpa using hnextAdj
  have htwo : ({previous, next} : Finset V).card = 2 := by
    simp [hpreviousNeNext]
  have hle := Finset.card_le_card hpairSubset
  rw [htwo, G.card_neighborFinset_eq_degree] at hle
  omega

private theorem extend_induced_spanningPath_from_leaf
    {V : Type uV} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {leaf neighbor : V} (hadj : G.Adj leaf neighbor)
    (hunique : ∀ other, G.Adj leaf other → other = neighbor)
    (path : SpanningPathOrder (G.induce ({leaf}ᶜ : Set V)))
    (tail : List ↑({leaf}ᶜ : Set V))
    (horder :
      path.order =
        (⟨neighbor, by simpa using hadj.ne.symm⟩ :
          ↑({leaf}ᶜ : Set V)) :: tail) :
    Nonempty (SpanningPathOrder G) := by
  let remainingNeighbor : ↑({leaf}ᶜ : Set V) :=
    ⟨neighbor, by simpa using hadj.ne.symm⟩
  let mappedTail := tail.map (fun vertex => vertex.1)
  have hpathNodup : (remainingNeighbor :: tail).Nodup := by
    rw [← horder]
    exact path.nodup
  have hmappedNodup : (neighbor :: mappedTail).Nodup := by
    have hmapped := hpathNodup.map
      (f := fun vertex : ↑({leaf}ᶜ : Set V) => vertex.1)
      (fun _ _ heq => Subtype.ext heq)
    simpa [remainingNeighbor, mappedTail] using hmapped
  refine ⟨{
    order := leaf :: neighbor :: mappedTail
    nodup := ?_
    complete := ?_
    chain := ?_
    covers := ?_
  }⟩
  · rw [List.nodup_cons]
    refine ⟨?_, hmappedNodup⟩
    intro hmem
    rcases List.mem_cons.mp hmem with heq | htail
    · exact hadj.ne heq
    · obtain ⟨other, _hotherMem, heq⟩ :=
        List.mem_map.mp (show leaf ∈ mappedTail from htail)
      exact other.2 (by simpa using heq)
  · intro vertex
    by_cases hleaf : vertex = leaf
    · simp [hleaf]
    · let remainingVertex : ↑({leaf}ᶜ : Set V) :=
        ⟨vertex, by simpa using hleaf⟩
      have hmem : remainingVertex ∈ remainingNeighbor :: tail := by
        rw [← horder]
        exact path.complete remainingVertex
      simp only [List.mem_cons] at hmem ⊢
      rcases hmem with heq | htail
      · right
        left
        exact congrArg Subtype.val heq
      · right
        right
        exact List.mem_map.mpr ⟨remainingVertex, htail, rfl⟩
  · have hpathChain :
        List.IsChain (G.induce ({leaf}ᶜ : Set V)).Adj
          (remainingNeighbor :: tail) := by
      rw [← horder]
      exact path.chain
    have hmappedChain :
        List.IsChain G.Adj (neighbor :: mappedTail) := by
      change List.IsChain G.Adj
        ((remainingNeighbor :: tail).map
          (fun vertex : ↑({leaf}ᶜ : Set V) => vertex.1))
      rw [List.isChain_map]
      simpa [remainingNeighbor, SimpleGraph.induce] using hpathChain
    exact .cons_cons hadj hmappedChain
  · intro left right hedge
    by_cases hleft : left = leaf
    · subst left
      have hright : right = neighbor := hunique right hedge
      subst right
      exact Or.inl ⟨[], mappedTail, by simp⟩
    by_cases hright : right = leaf
    · subst right
      have hleftEq : left = neighbor :=
        hunique left hedge.symm
      subst left
      exact Or.inr ⟨[], mappedTail, by simp⟩
    let remainingLeft : ↑({leaf}ᶜ : Set V) :=
      ⟨left, by simpa using hleft⟩
    let remainingRight : ↑({leaf}ᶜ : Set V) :=
      ⟨right, by simpa using hright⟩
    have hreducedAdj :
        (G.induce ({leaf}ᶜ : Set V)).Adj remainingLeft remainingRight :=
      hedge
    have hfullInfix :
        (neighbor :: mappedTail) <:+: leaf :: neighbor :: mappedTail :=
      ⟨[leaf], [], by simp⟩
    rcases path.covers hreducedAdj with hforward | hbackward
    · left
      have hmapped := hforward.map
        (fun vertex : ↑({leaf}ᶜ : Set V) => vertex.1)
      have hmapped' : [left, right] <:+: neighbor :: mappedTail := by
        rw [horder] at hmapped
        simpa [remainingLeft, remainingRight, remainingNeighbor,
          mappedTail] using hmapped
      exact hmapped'.trans hfullInfix
    · right
      have hmapped := hbackward.map
        (fun vertex : ↑({leaf}ᶜ : Set V) => vertex.1)
      have hmapped' : [right, left] <:+: neighbor :: mappedTail := by
        rw [horder] at hmapped
        simpa [remainingLeft, remainingRight, remainingNeighbor,
          mappedTail] using hmapped
      exact hmapped'.trans hfullInfix

private theorem tree_spanningPathOrder_aux :
    ∀ n : ℕ,
      ∀ (V : Type uV) [Fintype V] [DecidableEq V]
        (G : SimpleGraph V) [DecidableRel G.Adj],
        Fintype.card V = n →
        G.IsTree →
        (∀ vertex, G.degree vertex ≤ 2) →
        Nonempty (SpanningPathOrder G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro V _ _ G _ hcard htree hdegree
      classical
      by_cases hsubsingleton : Subsingleton V
      · let vertex : V := htree.connected.nonempty.some
        exact ⟨{
          order := [vertex]
          nodup := by simp
          complete := by
            intro other
            simp [Subsingleton.elim other vertex]
          chain := List.isChain_singleton vertex
          covers := by
            intro left right hadj
            exact False.elim (hadj.ne (Subsingleton.elim left right))
        }⟩
      · letI : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsubsingleton
        obtain ⟨leaf, hleafDegree⟩ :=
          htree.exists_vert_degree_one_of_nontrivial
        let remaining : Set V := {leaf}ᶜ
        let Remaining := ↑remaining
        let reduced : SimpleGraph Remaining := G.induce remaining
        have hreducedTree : reduced.IsTree := by
          refine ⟨?_, ?_⟩
          · exact htree.connected.induce_compl_singleton_of_degree_eq_one
              hleafDegree
          · exact htree.isAcyclic.induce remaining
        have hremainingCard : Fintype.card Remaining < n := by
          change Fintype.card {vertex : V // vertex ≠ leaf} < n
          rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq,
            ← hcard]
          exact Nat.sub_lt (Fintype.card_pos) Nat.zero_lt_one
        have hreducedDegree : ∀ vertex, reduced.degree vertex ≤ 2 := by
          intro vertex
          have hmap := G.map_neighborFinset_induce vertex
          have hcardMap := congrArg Finset.card hmap
          rw [Finset.card_map] at hcardMap
          rw [← reduced.card_neighborFinset_eq_degree,
            hcardMap]
          exact (Finset.card_le_card Finset.inter_subset_left).trans
            (hdegree vertex.1)
        obtain ⟨reducedPath⟩ :=
          ih (Fintype.card Remaining) hremainingCard
            Remaining reduced rfl hreducedTree hreducedDegree
        obtain ⟨neighbor, hleafNeighbor, hneighborUnique⟩ :=
          SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hleafDegree
        have hneighborNe : neighbor ≠ leaf := hleafNeighbor.ne.symm
        let remainingNeighbor : Remaining := ⟨neighbor, hneighborNe⟩
        have hremainingNeighborDegree :
            reduced.degree remainingNeighbor ≤ 1 := by
          have hmap := G.map_neighborFinset_induce remainingNeighbor
          have hcardMap := congrArg Finset.card hmap
          rw [Finset.card_map] at hcardMap
          have hleafMem : leaf ∈ G.neighborFinset neighbor := by
            simpa using hleafNeighbor.symm
          have hleafNotMem :
              leaf ∉ G.neighborFinset neighbor ∩ remaining.toFinset := by
            simp [remaining]
          have hstrict :
              (G.neighborFinset neighbor ∩ remaining.toFinset).card <
                (G.neighborFinset neighbor).card := by
            apply Finset.card_lt_card
            exact (Finset.ssubset_iff_of_subset
              Finset.inter_subset_left).mpr
                ⟨leaf, hleafMem, hleafNotMem⟩
          have hreducedLt :
              reduced.degree remainingNeighbor < G.degree neighbor := by
            rw [← reduced.card_neighborFinset_eq_degree,
              hcardMap, ← G.card_neighborFinset_eq_degree]
            exact hstrict
          have hneighborDegree := hdegree neighbor
          omega
        rcases spanningPath_endpoint_of_degree_le_one
            reduced reducedPath remainingNeighbor hremainingNeighborDegree with
          hfirst | hlast
        · obtain ⟨tail, horder⟩ := hfirst
          exact extend_induced_spanningPath_from_leaf G hleafNeighbor
            hneighborUnique
            reducedPath tail (by simpa [reduced, remaining, remainingNeighbor] using horder)
        · obtain ⟨initial, horder⟩ := hlast
          let reversedPath := reducedPath.reverse
          have hreversedFirst :
              ∃ tail, reversedPath.order = remainingNeighbor :: tail := by
            refine ⟨initial.reverse, ?_⟩
            change reducedPath.order.reverse =
              remainingNeighbor :: initial.reverse
            rw [horder]
            simp
          obtain ⟨tail, hreverseOrder⟩ := hreversedFirst
          exact extend_induced_spanningPath_from_leaf G hleafNeighbor
            hneighborUnique
            reversedPath tail
              (by simpa [reduced, remaining, remainingNeighbor] using
                hreverseOrder)

/-- Every finite tree of maximum degree two has a spanning path order. -/
theorem exists_spanningPathOrder_of_isTree_degree_le_two
    {V : Type uV} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (htree : G.IsTree) (hdegree : ∀ vertex, G.degree vertex ≤ 2) :
    Nonempty (SpanningPathOrder G) :=
  tree_spanningPathOrder_aux (Fintype.card V) V G rfl htree hdegree

end

end XORGame
end QIT

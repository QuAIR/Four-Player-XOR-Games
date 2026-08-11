/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Noncrossing
public import Mathlib.Data.List.Infix

/-!
# Deleting a disjoint family of adjacent equal-label pairs

This module isolates the list-theoretic step behind selected-block lifts.  A
functional symmetric relation pairs every selected vertex with a unique
selected mate.  If every such edge is adjacent in a duplicate-free order,
then the selected vertices occur as disjoint adjacent pairs.  Consequently,
any reduction of the unselected subword lifts to a reduction of the full
word.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uV uL

namespace InvolutionWord

/-- One list is obtained from another by finitely many equal-pair insertions. -/
inductive PairInsertionExtension {Letter : Type uL} :
    List Letter → List Letter → Prop
  | refl (word : List Letter) : PairInsertionExtension word word
  | insert (left right : List Letter) (letter : Letter) :
      PairInsertionExtension
        (left ++ right) (left ++ letter :: letter :: right)
  | trans {first second third : List Letter}
      (hfirst : PairInsertionExtension first second)
      (hsecond : PairInsertionExtension second third) :
      PairInsertionExtension first third

/-- Equal-pair insertion is stable under adding a common first letter. -/
theorem PairInsertionExtension.cons
    {Letter : Type uL} (head : Letter)
    {small large : List Letter}
    (hextension : PairInsertionExtension small large) :
    PairInsertionExtension (head :: small) (head :: large) := by
  induction hextension with
  | refl word => exact .refl (head :: word)
  | insert left right letter =>
      simpa using
        (PairInsertionExtension.insert
          (head :: left) right letter)
  | trans hfirst hsecond ihFirst ihSecond =>
      exact ihFirst.trans ihSecond

/-- Reducibility is preserved when adjacent equal pairs are inserted. -/
theorem PairInsertionExtension.reducesToEmpty
    {Letter : Type uL} {small large : List Letter}
    (hextension : PairInsertionExtension small large)
    (hsmall : ReducesToEmpty small) :
    ReducesToEmpty large := by
  induction hextension with
  | refl word => exact hsmall
  | insert left right letter =>
      exact ReducesToEmpty.insert left right letter hsmall
  | trans hfirst hsecond ihFirst ihSecond =>
      exact ihSecond (ihFirst hsmall)

/-- Equal-pair insertion preserves every integer alternating sum. -/
theorem PairInsertionExtension.alternatingSum_eq
    {Letter : Type uL} {small large : List Letter}
    (weight : Letter → ℤ)
    (hextension : PairInsertionExtension small large) :
    alternatingSum weight large = alternatingSum weight small := by
  induction hextension with
  | refl word => rfl
  | insert left right letter =>
      exact alternatingSum_insert_pair weight left right letter
  | trans hfirst hsecond ihFirst ihSecond =>
      exact ihSecond.trans ihFirst

/--
An explicit scan certificate: unselected vertices are kept, while selected
vertices occur in consecutive pairs carrying the same output label.
-/
inductive AdjacentSelectedPairing
    {Vertex : Type uV} {Letter : Type uL}
    (Selected : Vertex → Prop) (label : Vertex → Letter) :
    List Vertex → Prop
  | nil : AdjacentSelectedPairing Selected label []
  | keep (vertex : Vertex) (tail : List Vertex)
      (hunselected : ¬ Selected vertex)
      (htail : AdjacentSelectedPairing Selected label tail) :
      AdjacentSelectedPairing Selected label (vertex :: tail)
  | pair (left right : Vertex) (tail : List Vertex)
      (hleft : Selected left) (hright : Selected right)
      (hlabel : label left = label right)
      (htail : AdjacentSelectedPairing Selected label tail) :
      AdjacentSelectedPairing Selected label (left :: right :: tail)

/-- A scan certificate realizes the full word by equal-pair insertions. -/
theorem AdjacentSelectedPairing.pairInsertionExtension
    {Vertex : Type uV} {Letter : Type uL}
    {Selected : Vertex → Prop} [DecidablePred Selected]
    {label : Vertex → Letter} {order : List Vertex}
    (hpairing : AdjacentSelectedPairing Selected label order) :
    PairInsertionExtension
      ((order.filter fun vertex => ¬ Selected vertex).map label)
      (order.map label) := by
  induction hpairing with
  | nil => exact .refl []
  | keep vertex tail hunselected htail ih =>
      simpa [hunselected] using ih.cons (label vertex)
  | pair left right tail hleft hright hlabel htail ih =>
      have hinsert :
          PairInsertionExtension
            (tail.map label)
            (label left :: label left :: tail.map label) := by
        simpa using
          (PairInsertionExtension.insert
            [] (tail.map label) (label left))
      simpa [hleft, hright, hlabel] using ih.trans hinsert

/--
If the unselected subword reduces, then so does a word equipped with an
adjacent selected-pair scan.
-/
theorem AdjacentSelectedPairing.reducesToEmpty_of_filter
    {Vertex : Type uV} {Letter : Type uL}
    {Selected : Vertex → Prop} [DecidablePred Selected]
    {label : Vertex → Letter} {order : List Vertex}
    (hpairing : AdjacentSelectedPairing Selected label order)
    (hfiltered :
      ReducesToEmpty
        ((order.filter fun vertex => ¬ Selected vertex).map label)) :
    ReducesToEmpty (order.map label) :=
  hpairing.pairInsertionExtension.reducesToEmpty hfiltered

private theorem orderedPair_infix_tail
    {Vertex : Type uV} {head left right : Vertex}
    {tail : List Vertex}
    (hhead : head ≠ left)
    (hinfix : [left, right] <:+: head :: tail) :
    [left, right] <:+: tail := by
  rcases List.infix_cons_iff.mp hinfix with hprefix | hinfix
  · rcases List.prefix_cons_iff.mp hprefix with hempty | ⟨rest, heq, _⟩
    · simp at hempty
    · simp at heq
      exact False.elim (hhead heq.1.symm)
  · exact hinfix

private theorem pairCover_infix_tail
    {Vertex : Type uV} {head left right : Vertex}
    {tail : List Vertex}
    (hleft : head ≠ left) (hright : head ≠ right)
    (hcover :
      [left, right] <:+: head :: tail ∨
        [right, left] <:+: head :: tail) :
    [left, right] <:+: tail ∨ [right, left] <:+: tail := by
  rcases hcover with hforward | hbackward
  · exact Or.inl (orderedPair_infix_tail hleft hforward)
  · exact Or.inr (orderedPair_infix_tail hright hbackward)

private theorem head_pair_of_cover
    {Vertex : Type uV} {head mate : Vertex} {tail : List Vertex}
    (hnodup : (head :: tail).Nodup) (hne : head ≠ mate)
    (hcover :
      [head, mate] <:+: head :: tail ∨
        [mate, head] <:+: head :: tail) :
    ∃ rest, tail = mate :: rest := by
  rcases hcover with hforward | hbackward
  · rcases List.infix_cons_iff.mp hforward with hprefix | hinfix
    · rcases hprefix with ⟨rest, heq⟩
      simp at heq
      exact ⟨rest, heq.symm⟩
    · exact False.elim (hnodup.notMem (hinfix.mem (by simp)))
  · rcases List.infix_cons_iff.mp hbackward with hprefix | hinfix
    · rcases hprefix with ⟨rest, heq⟩
      simp at heq
      exact False.elim (hne heq.1.symm)
    · exact False.elim (hnodup.notMem (hinfix.mem (by simp)))

/--
Abstract adjacent-pair decomposition theorem.  It converts relational data
(symmetric unique mates whose edges are covered by the order) into the
explicit left-to-right scan used by `AdjacentSelectedPairing`.
-/
theorem adjacentSelectedPairing_of_unique_adjacent_mates
    {Vertex : Type uV} {Letter : Type uL}
    (Selected : Vertex → Prop) (label : Vertex → Letter)
    (Mate : Vertex → Vertex → Prop)
    (hsymm : ∀ {left right}, Mate left right → Mate right left)
    (hne : ∀ {left right}, Mate left right → left ≠ right)
    (hselected :
      ∀ {left right}, Mate left right →
        Selected left ∧ Selected right)
    (hlabel :
      ∀ {left right}, Mate left right → label left = label right)
    (hfunctional :
      ∀ {vertex first second},
        Mate vertex first → Mate vertex second → first = second) :
    ∀ order : List Vertex,
      order.Nodup →
      (∀ vertex, vertex ∈ order → Selected vertex →
        ∃ mate, mate ∈ order ∧ Mate vertex mate) →
      (∀ {left right}, left ∈ order → right ∈ order →
        Mate left right →
          [left, right] <:+: order ∨ [right, left] <:+: order) →
      AdjacentSelectedPairing Selected label order
  | [], _hnodup, _htotal, _hcover => .nil
  | head :: tail, hnodup, htotal, hcover => by
      by_cases hhead : Selected head
      · obtain ⟨mate, hmateMem, hmate⟩ :=
          htotal head (by simp) hhead
        have hmateNe : head ≠ mate := hne hmate
        obtain ⟨rest, htail⟩ :=
          head_pair_of_cover hnodup hmateNe
            (hcover (by simp) hmateMem hmate)
        subst tail
        have hmateSelected : Selected mate := (hselected hmate).2
        have hmateLabel : label head = label mate := hlabel hmate
        have hrestNodup : rest.Nodup := hnodup.tail.tail
        have hheadNotMem : head ∉ rest := by
          intro hmem
          exact hnodup.notMem (by simp [hmem])
        have hmateNotMem : mate ∉ rest :=
          List.Nodup.notMem hnodup.tail
        apply AdjacentSelectedPairing.pair
          head mate rest hhead hmateSelected hmateLabel
        apply adjacentSelectedPairing_of_unique_adjacent_mates
          Selected label Mate hsymm hne hselected hlabel hfunctional
          rest hrestNodup
        · intro vertex hvertex hvertexSelected
          obtain ⟨partner, hpartnerMem, hpartner⟩ :=
            htotal vertex (by simp [hvertex]) hvertexSelected
          have hpartnerHead : partner ≠ head := by
            intro heq
            subst partner
            have hheadVertex : Mate head vertex := hsymm hpartner
            have hmatevertex : mate = vertex :=
              hfunctional hmate hheadVertex
            exact hmateNotMem (hmatevertex ▸ hvertex)
          have hpartnerMate : partner ≠ mate := by
            intro heq
            subst partner
            have hmateVertex : Mate mate vertex := hsymm hpartner
            have hheadVertex : Mate mate head := hsymm hmate
            have hheadEq : head = vertex :=
              hfunctional hheadVertex hmateVertex
            exact hheadNotMem (hheadEq ▸ hvertex)
          refine ⟨partner, ?_, hpartner⟩
          simpa [hpartnerHead, hpartnerMate] using hpartnerMem
        · intro left right hleft hright hrel
          have hglobal := hcover
            (left := left) (right := right)
            (by simp [hleft]) (by simp [hright]) hrel
          have hheadLeft : head ≠ left := by
            intro heq
            exact hheadNotMem (heq ▸ hleft)
          have hheadRight : head ≠ right := by
            intro heq
            exact hheadNotMem (heq ▸ hright)
          have hafterHead :=
            pairCover_infix_tail hheadLeft hheadRight hglobal
          have hmateLeft : mate ≠ left := by
            intro heq
            exact hmateNotMem (heq ▸ hleft)
          have hmateRight : mate ≠ right := by
            intro heq
            exact hmateNotMem (heq ▸ hright)
          exact pairCover_infix_tail
            hmateLeft hmateRight hafterHead
      · apply AdjacentSelectedPairing.keep head tail hhead
        apply adjacentSelectedPairing_of_unique_adjacent_mates
          Selected label Mate hsymm hne hselected hlabel hfunctional
          tail hnodup.tail
        · intro vertex hvertex hvertexSelected
          obtain ⟨mate, hmateMem, hmate⟩ :=
            htotal vertex (by simp [hvertex]) hvertexSelected
          have hmateNe : mate ≠ head := by
            intro heq
            subst mate
            exact hhead (hselected hmate).2
          exact ⟨mate, by simpa [hmateNe] using hmateMem, hmate⟩
        · intro left right hleft hright hrel
          have hheadLeft : head ≠ left := by
            intro heq
            exact hnodup.notMem (heq ▸ hleft)
          have hheadRight : head ≠ right := by
            intro heq
            exact hnodup.notMem (heq ▸ hright)
          exact pairCover_infix_tail hheadLeft hheadRight <|
            hcover (by simp [hleft]) (by simp [hright]) hrel
termination_by order => order.length

end InvolutionWord

end XORGame
end QIT

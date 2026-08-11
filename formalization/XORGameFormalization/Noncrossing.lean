/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Lift

/-!
# Noncrossing equal-letter matchings

This module packages the reusable combinatorial core of the simultaneous
matching formulation.  A noncrossing perfect matching of equal letters has a
Catalan recursion: the partner of the first letter separates an inner and an
outer matched interval.  Such a matching gives an exact adjacent-cancellation
proof.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uQ uR

namespace InvolutionWord

/--
If `middle` reduces to empty, it may be inserted into any context which
already reduces to empty.
-/
theorem ReducesToEmpty.insert_reducible_middle
    {Letter : Type uQ} {left middle right : List Letter}
    (hmiddle : ReducesToEmpty middle)
    (hcontext : ReducesToEmpty (left ++ right)) :
    ReducesToEmpty (left ++ middle ++ right) := by
  induction hmiddle with
  | nil =>
      simpa using hcontext
  | insert before after letter reduced ih =>
      have hbase :
          ReducesToEmpty ((left ++ before) ++ (after ++ right)) := by
        simpa [List.append_assoc] using ih
      simpa [List.append_assoc] using
        ReducesToEmpty.insert
          (left ++ before) (after ++ right) letter hbase

/-- A map of letters preserves exact involution-word reduction. -/
theorem ReducesToEmpty.map
    {Letter : Type uQ} {Letter' : Type uR}
    (f : Letter → Letter') {word : List Letter}
    (hword : ReducesToEmpty word) :
    ReducesToEmpty (word.map f) := by
  induction hword with
  | nil =>
      exact ReducesToEmpty.nil
  | insert left right letter reduced ih =>
      have ih' :
          ReducesToEmpty (left.map f ++ right.map f) := by
        simpa [List.map_append] using ih
      simpa [List.map_append] using
        ReducesToEmpty.insert
          (left.map f) (right.map f) (f letter) ih'

end InvolutionWord

/--
An inductive presentation of a noncrossing perfect matching whose endpoints
carry equal labels.

In the `pair` constructor, the two displayed copies of `letter` are matched.
The recursively matched `inside` interval lies below that outer arc, while
`outside` is disjoint from it.
-/
inductive NoncrossingEqualMatching {Letter : Type uQ} :
    List Letter → Prop
  | nil : NoncrossingEqualMatching []
  | pair (letter : Letter) (inside outside : List Letter)
      (insideMatching : NoncrossingEqualMatching inside)
      (outsideMatching : NoncrossingEqualMatching outside) :
      NoncrossingEqualMatching
        (letter :: inside ++ letter :: outside)

/--
Every noncrossing perfect matching of equal labels supplies a complete
adjacent-pair involution reduction.
-/
theorem NoncrossingEqualMatching.reducesToEmpty
    {Letter : Type uQ} {word : List Letter}
    (hmatching : NoncrossingEqualMatching word) :
    InvolutionWord.ReducesToEmpty word := by
  induction hmatching with
  | nil =>
      exact InvolutionWord.ReducesToEmpty.nil
  | pair letter inside outside _ _ insideIH outsideIH =>
      have hpair :
          InvolutionWord.ReducesToEmpty
            ([letter] ++ letter :: outside) := by
        simpa using
          InvolutionWord.ReducesToEmpty.insert
            [] outside letter outsideIH
      simpa [List.append_assoc] using
        insideIH.insert_reducible_middle hpair

end XORGame
end QIT

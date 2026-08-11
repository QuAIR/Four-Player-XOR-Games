/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Refutation
public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.TakeDrop

/-!
# Alternating cancellation over at most two letters

An even signed occurrence order alternates positive and negative positions.
On a page using at most two question labels, equality of the signed count of
each label forces the projected word to reduce by adjacent equal-letter
cancellations.  This is the binary-page cancellation lemma used after one
selected ternary block has been removed.
-/

@[expose] public section

namespace QIT
namespace XORGame
namespace InvolutionWord

universe uQ

private theorem eq_of_mem_card_le_two
    {Letter : Type uQ} [DecidableEq Letter]
    (letters : Finset Letter) (hcard : letters.card ≤ 2)
    {a b c : Letter}
    (ha : a ∈ letters) (hb : b ∈ letters) (hc : c ∈ letters)
    (hab : a ≠ b) (hbc : b ≠ c) :
    c = a := by
  by_contra hca
  have hthree : ({a, b, c} : Finset Letter).card = 3 := by
    calc
      ({a, b, c} : Finset Letter).card =
          ({b, c} : Finset Letter).card + 1 :=
        Finset.card_insert_of_notMem (by
          simpa [hab, Ne.symm hca])
      _ = ({c} : Finset Letter).card + 1 + 1 := by
        rw [Finset.card_insert_of_notMem (by simpa using hbc)]
      _ = 3 := by simp
  have hsubset : ({a, b, c} : Finset Letter) ⊆ letters := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have := Finset.card_le_card hsubset
  omega

private theorem alternatingSum_indicator_pos_of_isChain_ne
    {Letter : Type uQ} [DecidableEq Letter]
    (letters : Finset Letter) (hcard : letters.card ≤ 2)
    (a : Letter) :
    ∀ tail : List Letter,
      a ∈ letters →
      (∀ x ∈ tail, x ∈ letters) →
      List.IsChain (· ≠ ·) (a :: tail) →
      0 < alternatingSum (fun x => if x = a then 1 else 0) (a :: tail)
  | [], _ha, _htail, _hchain => by
      simp [alternatingSum]
  | [b], ha, htail, hchain => by
      have hab : a ≠ b := by
        simpa using hchain
      simp [alternatingSum, Ne.symm hab]
  | b :: c :: tail, ha, htail, hchain => by
      have hab : a ≠ b := by
        simpa using hchain.rel
      have hrest : List.IsChain (· ≠ ·) (b :: c :: tail) :=
        hchain.tail
      have hbc : b ≠ c := by
        simpa using hrest.rel
      have hb : b ∈ letters := htail b (by simp)
      have hc : c ∈ letters := htail c (by simp)
      have hca : c = a :=
        eq_of_mem_card_le_two letters hcard ha hb hc hab hbc
      subst c
      have htail' : ∀ x ∈ tail, x ∈ letters := by
        intro x hx
        exact htail x (by simp [hx])
      have hchain' : List.IsChain (· ≠ ·) (a :: tail) :=
        hrest.tail
      have ih :=
        alternatingSum_indicator_pos_of_isChain_ne
          letters hcard a tail ha htail' hchain'
      simp only [alternatingSum] at ih ⊢
      simp only [if_pos, if_neg (Ne.symm hab), sub_zero]
      omega

/--
If at most two letters occur and every letter has alternating signed sum
zero, the word reduces to the empty word by adjacent equal-pair deletion.
-/
theorem reducesToEmpty_of_toFinset_card_le_two_of_alternatingSum_zero
    {Letter : Type uQ} [DecidableEq Letter]
    (word : List Letter)
    (hcard : word.toFinset.card ≤ 2)
    (hzero :
      ∀ letter : Letter,
        alternatingSum (fun x => if x = letter then 1 else 0) word = 0) :
    ReducesToEmpty word := by
  by_cases hchain : List.IsChain (· ≠ ·) word
  · cases word with
    | nil => exact .nil
    | cons a tail =>
        have hpos :=
          alternatingSum_indicator_pos_of_isChain_ne
            (a :: tail).toFinset hcard a tail
              (by simp) (by
                intro x hx
                exact List.mem_toFinset.mpr (List.mem_cons_of_mem a hx))
              hchain
        exact False.elim <| by
          rw [hzero a] at hpos
          omega
  · obtain ⟨n, hn, heq⟩ :=
      List.exists_not_getElem_of_not_isChain hchain
    have hn0 : n < word.length := by omega
    have hn1 : n + 1 < word.length := hn
    have hletters : word[n] = word[n + 1] := by
      simpa using heq
    let left := word.take n
    let right := word.drop (n + 2)
    let shorter := left ++ right
    have hdecomp :
        word = left ++ word[n] :: word[n] :: right := by
      calc
        word = word.take n ++ word.drop n :=
          (List.take_append_drop n word).symm
        _ = word.take n ++ word[n] :: word.drop (n + 1) := by
          rw [List.drop_eq_getElem_cons hn0]
        _ = word.take n ++ word[n] :: word[n + 1] ::
              word.drop (n + 2) := by
          rw [List.drop_eq_getElem_cons hn1]
        _ = left ++ word[n] :: word[n] :: right := by
          rw [hletters]
    have hshorterCard : shorter.toFinset.card ≤ 2 := by
      apply (Finset.card_le_card ?_).trans hcard
      intro letter hletter
      simp only [shorter, List.mem_toFinset, List.mem_append] at hletter
      simp only [List.mem_toFinset]
      rcases hletter with hleft | hright
      · exact List.mem_of_mem_take hleft
      · exact List.mem_of_mem_drop hright
    have hshorterZero :
        ∀ letter : Letter,
          alternatingSum (fun x => if x = letter then 1 else 0)
            shorter = 0 := by
      intro letter
      rw [hdecomp] at hzero
      exact
        (alternatingSum_insert_pair
          (fun x => if x = letter then 1 else 0)
          left right word[n]).symm.trans (hzero letter)
    rw [hdecomp]
    apply ReducesToEmpty.insert left right word[n]
    exact reducesToEmpty_of_toFinset_card_le_two_of_alternatingSum_zero
      shorter hshorterCard hshorterZero
termination_by word.length
decreasing_by
  simp only [shorter, left, right, List.length_append,
    List.length_take, List.length_drop]
  rw [min_eq_left (Nat.le_of_lt hn0)]
  omega

end InvolutionWord
end XORGame
end QIT

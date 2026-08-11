/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.GeneralObservableStrategy
public import XORGameFormalization.SemanticCompletion.GameNormalization
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Tactic

/-!
# Generic game-group duality

This module formalizes the presented group of a finite XOR game and the
regular representation used to turn the absence of operator refutations into
an exact perfect commuting-operator strategy.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace QIT
namespace XORGame

universe uQ uM uL uN

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

namespace InvolutionWord

/-- Deleting an adjacent equal pair preserves reducibility to the empty word. -/
theorem reducesToEmpty_delete {Letter : Type uL}
    {left right : List Letter} {q : Letter}
    (h : ReducesToEmpty (left ++ q :: q :: right)) :
    ReducesToEmpty (left ++ right) := by
  have helper : ∀ {large : List Letter}, ReducesToEmpty large →
      ∀ {left right : List Letter} {q : Letter},
        large = left ++ q :: q :: right → ReducesToEmpty (left ++ right) := by
    intro large h
    induction h with
    | nil =>
        intro left right q hEq
        have hlen : (0 : ℕ) = left.length + 1 + 1 + right.length := by
          simpa using congrArg List.length hEq.symm
        omega
    | insert l1 l2 x reduced ih =>
        intro left right q hEq
        have hEq' : left ++ q :: q :: right = l1 ++ x :: x :: l2 := hEq.symm
        by_cases hA : left.length + 2 ≤ l1.length
        · -- the q-pair lies inside l1 (strictly before the x-pair)
          let rest := l1.drop (left.length + 2)
          have hl1 : l1 = left ++ q :: q :: rest := by
            calc
              l1 = (left ++ q :: q :: right).take l1.length := by
                    rw [hEq']
                    simpa
              _ = (left ++ q :: q :: right).take
                    (left.length + 2 + (l1.length - (left.length + 2))) := by
                    congr 1
                    omega
              _ = (left ++ q :: q :: right).take (left.length + 2) ++
                    ((left ++ q :: q :: right).drop (left.length + 2)).take
                      (l1.length - (left.length + 2)) := by
                    rw [List.take_add]
              _ = (left ++ q :: q :: right).take (left.length + 2) ++
                    ((l1 ++ x :: x :: l2).drop (left.length + 2)).take
                      (l1.length - (left.length + 2)) := by
                    rw [hEq']
              _ = (left ++ q :: q :: right).take (left.length + 2) ++
                    ((l1.drop (left.length + 2) ++ x :: x :: l2)).take
                      (l1.length - (left.length + 2)) := by
                    rw [List.drop_append_of_le_length hA]
              _ = left ++ q :: q :: rest := by
                    have htake1 : (left ++ q :: q :: right).take (left.length + 2) =
                        left ++ [q, q] := by
                      rw [List.take_add (i := left.length) (j := 2)]
                      have h1 : (left ++ q :: q :: right).take left.length = left := by
                        rw [List.take_append_of_le_length (le_refl _)]
                        simp
                      have h2 : (left ++ q :: q :: right).drop left.length =
                          q :: q :: right := by
                        rw [List.drop_append_of_le_length (le_refl _)]
                        simp
                      rw [h1, h2]
                      simp
                    have hlen_rest : l1.length - (left.length + 2) =
                        (l1.drop (left.length + 2)).length := by
                      dsimp
                      rw [List.length_drop]
                    have htake2 : ((l1.drop (left.length + 2) ++ x :: x :: l2)).take
                        (l1.length - (left.length + 2)) = l1.drop (left.length + 2) := by
                      rw [hlen_rest]
                      rw [List.take_append_of_le_length
                        (show (l1.drop (left.length + 2)).length ≤
                          (l1.drop (left.length + 2)).length from le_rfl)]
                      simp
                    rw [htake1, htake2]
                    simp [rest]
          have hright : right = rest ++ x :: x :: l2 := by
            calc
              right = (left ++ q :: q :: right).drop (left.length + 2) := by
                      have h1 : (left ++ q :: q :: right).drop left.length =
                          q :: q :: right := by
                        have hdrop : (left ++ q :: q :: right).drop left.length =
                            left.drop left.length ++ (q :: q :: right) := by
                          rw [List.drop_append_of_le_length (le_refl _)]
                        rw [hdrop]
                        simp
                      have h2 : (left ++ q :: q :: right).drop (left.length + 2) =
                          (q :: q :: right).drop 2 := by
                        rw [← List.drop_drop]
                        rw [h1]
                      rw [h2]
                      rfl
              _ = (l1 ++ x :: x :: l2).drop (left.length + 2) := by rw [hEq']
              _ = l1.drop (left.length + 2) ++ x :: x :: l2 := by
                      rw [List.drop_append_of_le_length hA]
              _ = rest ++ x :: x :: l2 := rfl
          have hred : ReducesToEmpty (left ++ rest ++ l2) := by
            have harg : l1 ++ l2 = left ++ q :: q :: (rest ++ l2) := by
              rw [hl1]
              simp [List.append_assoc]
            simpa [List.append_assoc] using
              ih (left := left) (right := rest ++ l2) (q := q) harg
          have hgoal : left ++ right = left ++ rest ++ x :: x :: l2 := by
            rw [hright]
            simp [List.append_assoc]
          rw [hgoal]
          exact ReducesToEmpty.insert (left ++ rest) l2 x hred
        · by_cases hB : l1.length + 2 ≤ left.length
          · -- the q-pair lies inside l2 (strictly after the x-pair)
            let rest := l2.take (left.length - (l1.length + 2))
            have hdropxx : (l1 ++ x :: x :: l2).drop (l1.length + 2) = l2 := by
              have h1 : (l1 ++ x :: x :: l2).drop l1.length = x :: x :: l2 := by
                rw [List.drop_append_of_le_length (le_refl _)]
                simp
              rw [← List.drop_drop]
              rw [h1]
              rfl
            have hleft : left = l1 ++ x :: x :: rest := by
              calc
                left = (left ++ q :: q :: right).take left.length := by simp
                _ = (l1 ++ x :: x :: l2).take left.length := by rw [hEq']
                _ = (l1 ++ x :: x :: l2).take
                      (l1.length + 2 + (left.length - (l1.length + 2))) := by
                      congr 1
                      omega
                _ = (l1 ++ x :: x :: l2).take (l1.length + 2) ++
                      ((l1 ++ x :: x :: l2).drop (l1.length + 2)).take
                        (left.length - (l1.length + 2)) := by
                      rw [List.take_add]
                _ = (l1 ++ x :: x :: l2).take (l1.length + 2) ++
                      l2.take (left.length - (l1.length + 2)) := by
                      rw [hdropxx]
                _ = l1 ++ x :: x :: rest := by
                      have htake : (l1 ++ x :: x :: l2).take (l1.length + 2) =
                          l1 ++ [x, x] := by
                        rw [List.take_add (i := l1.length) (j := 2)]
                        have h1 : (l1 ++ x :: x :: l2).take l1.length = l1 := by
                          rw [List.take_append_of_le_length (le_refl _)]
                          simp
                        have h2 : (l1 ++ x :: x :: l2).drop l1.length = x :: x :: l2 := by
                          rw [List.drop_append_of_le_length (le_refl _)]
                          simp
                        rw [h1, h2]
                        simp
                      rw [htake]
                      simp [List.append_assoc, rest]
            have hldrop : left.drop (l1.length + 2) = rest := by
              rw [hleft]
              have h1 : (l1 ++ x :: x :: rest).drop l1.length = x :: x :: rest := by
                rw [List.drop_append_of_le_length (le_refl _)]
                simp
              rw [← List.drop_drop]
              rw [h1]
              rfl
            have hl2 : l2 = rest ++ q :: q :: right := by
              calc
                l2 = (l1 ++ x :: x :: l2).drop (l1.length + 2) := by
                      rw [hdropxx]
                _ = (left ++ q :: q :: right).drop (l1.length + 2) := by rw [← hEq']
                _ = left.drop (l1.length + 2) ++ q :: q :: right := by
                      rw [List.drop_append_of_le_length hB]
                _ = rest ++ q :: q :: right := by rw [hldrop]
            have hred : ReducesToEmpty (l1 ++ rest ++ right) := by
              have harg : l1 ++ l2 = (l1 ++ rest) ++ q :: q :: right := by
                rw [hl2]
                simp [List.append_assoc]
              simpa [List.append_assoc] using
                ih (left := l1 ++ rest) (right := right) (q := q) harg
            have hgoal : left ++ right = l1 ++ (x :: x :: rest) ++ right := by
              rw [hleft]
            rw [hgoal]
            simpa [List.append_assoc] using
              ReducesToEmpty.insert l1 (rest ++ right) x
                (by simpa [List.append_assoc] using hred)
          · -- the two pairs are equal or overlap: deleting either gives the same list
            let L := left ++ q :: q :: right
            have hL : L = l1 ++ x :: x :: l2 := hEq.symm
            have hcases : left.length = l1.length ∨
                left.length = l1.length + 1 ∨ l1.length = left.length + 1 := by omega
            rcases hcases with hlen | hlen | hlen
            · -- equal lengths: left = l1, right = l2
              have hleft_eq : left = l1 := by
                calc
                  left = (left ++ q :: q :: right).take left.length := by simp
                  _ = (l1 ++ x :: x :: l2).take left.length := by rw [hEq']
                  _ = (l1 ++ x :: x :: l2).take l1.length := by rw [hlen]
                  _ = l1 := by
                        rw [List.take_append_of_le_length (le_refl _)]
                        simp
              have hright_eq : right = l2 := by
                calc
                  right = (left ++ q :: q :: right).drop (left.length + 2) := by
                          have h1 : (left ++ q :: q :: right).drop left.length =
                              q :: q :: right := by
                            have hd : (left ++ q :: q :: right).drop left.length =
                                left.drop left.length ++ (q :: q :: right) := by
                              rw [List.drop_append_of_le_length (le_refl _)]
                            rw [hd]
                            simp
                          have h2 : (left ++ q :: q :: right).drop (left.length + 2) =
                              (q :: q :: right).drop 2 := by
                            rw [← List.drop_drop]
                            rw [h1]
                          rw [h2]
                          rfl
                  _ = (l1 ++ x :: x :: l2).drop (left.length + 2) := by rw [hEq']
                  _ = (l1 ++ x :: x :: l2).drop (l1.length + 2) := by rw [hlen]
                  _ = l2 := by
                        have h1 : (l1 ++ x :: x :: l2).drop l1.length = x :: x :: l2 := by
                          rw [List.drop_append_of_le_length (le_refl _)]
                          simp
                        rw [← List.drop_drop]
                        rw [h1]
                        rfl
              rw [hleft_eq, hright_eq]
              exact reduced
            · -- left has one more letter than l1: x = q, left = l1 ++ [x], l2 = q :: right
              have hx_pos : l1.length < (left ++ q :: q :: right).length := by
                simp [hlen]
                omega
              have hx0 : (left ++ q :: q :: right)[l1.length]'hx_pos = x := by
                have hq' : (left ++ q :: q :: right)[l1.length]? = some x := by
                  rw [hEq']
                  simp
                have hs := (List.getElem?_eq_getElem hx_pos).symm.trans hq'
                simpa using hs
              have hq_pos : l1.length + 1 < (left ++ q :: q :: right).length := by
                simp [hlen]
              have hq0 : (left ++ q :: q :: right)[l1.length + 1]'hq_pos = q := by
                have hq' : (left ++ q :: q :: right)[l1.length + 1]? = some q := by
                  simp [hlen]
                have hs := (List.getElem?_eq_getElem hq_pos).symm.trans hq'
                simpa using hs
              have hx1 : (left ++ q :: q :: right)[l1.length + 1]'hq_pos = x := by
                have hq' : (left ++ q :: q :: right)[l1.length + 1]? = some x := by
                  have hpos : l1.length + 1 = l1.length + 1 := rfl
                  rw [hEq']
                  simp
                have hs := (List.getElem?_eq_getElem hq_pos).symm.trans hq'
                simpa using hs
              have hxq : x = q := by
                exact (hx0.symm.trans (hx0.trans hx1.symm)).trans hq0
              have hfirst : (L.drop l1.length).take 1 = [x] := by
                have hd : L.drop l1.length = x :: x :: l2 := by
                  rw [hL]
                  rw [List.drop_append_of_le_length (le_refl _)]
                  simp
                rw [hd]
                rfl
              have hleft' : left = l1 ++ [x] := by
                calc
                  left = L.take left.length := by simp [L]
                  _ = L.take (l1.length + 1) := by rw [hlen]
                  _ = L.take l1.length ++ (L.drop l1.length).take 1 := by
                        rw [List.take_add (i := l1.length) (j := 1)]
                  _ = l1 ++ (L.drop l1.length).take 1 := by
                        have ht : L.take l1.length = l1 := by
                          rw [hL]
                          rw [List.take_append_of_le_length (le_refl _)]
                          simp
                        rw [ht]
                  _ = l1 ++ [x] := by rw [hfirst]
              have hl2' : l2 = q :: right := by
                calc
                  l2 = L.drop (l1.length + 2) := by
                        rw [hL]
                        have h1 : (l1 ++ x :: x :: l2).drop l1.length = x :: x :: l2 := by
                          rw [List.drop_append_of_le_length (le_refl _)]
                          simp
                        rw [← List.drop_drop]
                        rw [h1]
                        rfl
                  _ = (left ++ q :: q :: right).drop (left.length + 1) := by
                        congr 1
                        omega
                  _ = q :: right := by
                        have hd : (left ++ q :: q :: right).drop left.length =
                            q :: q :: right := by
                          have hdd : (left ++ q :: q :: right).drop left.length =
                              left.drop left.length ++ (q :: q :: right) := by
                            rw [List.drop_append_of_le_length (le_refl _)]
                          rw [hdd]
                          simp
                        have hdrop1 : (left ++ q :: q :: right).drop (left.length + 1) =
                            (q :: q :: right).drop 1 := by
                          rw [← List.drop_drop]
                          rw [hd]
                        rw [hdrop1]
                        rfl
              rw [hleft']
              rw [hxq]
              have hgoal' : (l1 ++ [q]) ++ right = l1 ++ l2 := by
                rw [hl2']
                simp [List.append_assoc]
              rw [hgoal']
              exact reduced
            · -- l1 has one more letter than left: q = x, l1 = left ++ [q], right = q :: l2
              have hq0_pos : left.length < (left ++ q :: q :: right).length := by
                simp
              have hq0' : (left ++ q :: q :: right)[left.length]'hq0_pos = q := by
                have hq' : (left ++ q :: q :: right)[left.length]? = some q := by
                  simp
                have hs := (List.getElem?_eq_getElem hq0_pos).symm.trans hq'
                simpa using hs
              have hq1_pos : left.length + 2 < (left ++ q :: q :: right).length := by
                have hlenL : (left ++ q :: q :: right).length = l1.length + 2 + l2.length := by
                  rw [hEq']
                  simp
                  omega
                rw [hlenL]
                omega
              have hx1' : (left ++ q :: q :: right)[left.length + 2]'hq1_pos = x := by
                have hq' : (left ++ q :: q :: right)[left.length + 2]? = some x := by
                  have hpos : left.length + 2 = l1.length + 1 := by omega
                  rw [hpos]
                  rw [hEq']
                  simp
                have hs := (List.getElem?_eq_getElem hq1_pos).symm.trans hq'
                simpa using hs
              have hxq' : x = q := by
                have hq2_pos : left.length + 1 < (left ++ q :: q :: right).length := by
                  have hlenL : (left ++ q :: q :: right).length = l1.length + 2 + l2.length := by
                    rw [hEq']
                    simp
                    omega
                  rw [hlenL]
                  omega
                have hq2 : (left ++ q :: q :: right)[left.length + 1]'hq2_pos = q := by
                  have hq' : (left ++ q :: q :: right)[left.length + 1]? = some q := by
                    simp
                  have hs := (List.getElem?_eq_getElem hq2_pos).symm.trans hq'
                  simpa using hs
                have hx2 : (left ++ q :: q :: right)[left.length + 1]'hq2_pos = x := by
                  have hq' : (left ++ q :: q :: right)[left.length + 1]? = some x := by
                    have hpos : left.length + 1 = l1.length := by omega
                    rw [hpos]
                    rw [hEq']
                    simp
                  have hs := (List.getElem?_eq_getElem hq2_pos).symm.trans hq'
                  simpa using hs
                exact hx2.symm.trans hq2
              have hl1' : l1 = left ++ [q] := by
                calc
                  l1 = L.take l1.length := by
                        rw [hL]
                        rw [List.take_append_of_le_length (le_refl _)]
                        simp
                  _ = L.take (left.length + 1) := by congr 1
                  _ = L.take left.length ++ (L.drop left.length).take 1 := by
                        rw [List.take_add (i := left.length) (j := 1)]
                  _ = left ++ (L.drop left.length).take 1 := by
                        have ht : L.take left.length = left := by
                          simp [L]
                        rw [ht]
                  _ = left ++ [q] := by
                        have hd : L.drop left.length = q :: q :: right := by
                          simp [L]
                        have ht1 : (q :: q :: right).take 1 = [q] := rfl
                        rw [hd, ht1]
              have hright' : right = q :: l2 := by
                calc
                  right = L.drop (left.length + 2) := by simp [L]
                  _ = x :: L.drop (left.length + 3) := by
                        rw [List.drop_eq_getElem_cons hq1_pos]
                        congr 1
                  _ = x :: l2 := by
                        congr 1
                        have hd : L.drop (l1.length + 2) = l2 := by
                          rw [hL]
                          have h1 : (l1 ++ x :: x :: l2).drop l1.length = x :: x :: l2 := by
                            rw [List.drop_append_of_le_length (le_refl _)]
                            simp
                          rw [← List.drop_drop]
                          rw [h1]
                          rfl
                        have hlen3 : l1.length + 2 = left.length + 3 := by omega
                        rw [← hlen3]
                        exact hd
                  _ = q :: l2 := by rw [hxq']
              have hgoal' : left ++ right = l1 ++ l2 := by
                rw [hright']
                rw [hl1']
                simp [List.append_assoc]
              rw [hgoal']
              exact reduced

  exact helper h rfl

private def Reduced {Q : Type uL} (w : List Q) : Prop := w.IsChain (· ≠ ·)

/-- The toggle of a letter on an involution stack. -/
private def toggle {Q : Type uL} [DecidableEq Q] (q : Q) (w : List Q) : List Q :=
  if hw : w = [] then [q]
  else if hlast : w.getLast? = some q then w.dropLast
  else w ++ [q]

private theorem toggle_empty {Q : Type uL} [DecidableEq Q] (q : Q) :
    toggle q ([] : List Q) = [q] := by simp [toggle]
private theorem toggle_last {Q : Type uL} [DecidableEq Q] {q : Q} {w : List Q}
    (hw : w ≠ []) (hlast : w.getLast? = some q) : toggle q w = w.dropLast := by
  simp [toggle, hw, hlast]
private theorem toggle_not_last {Q : Type uL} [DecidableEq Q] {q : Q} {w : List Q}
    (hw : w ≠ []) (hlast : w.getLast? ≠ some q) : toggle q w = w ++ [q] := by
  simp [toggle, hw, hlast]
private theorem toggle_push {Q : Type uL} [DecidableEq Q] {q : Q} {w : List Q}
    (h : w = [] ∨ w.getLast? ≠ some q) : toggle q w = w ++ [q] := by
  rcases h with hw0 | hlast
  · rw [hw0, toggle_empty]; simp
  · by_cases hw0' : w = []
    · rw [hw0', toggle_empty]; simp
    · exact toggle_not_last hw0' hlast

private theorem reduced_append {Q : Type uL} {q : Q} {w : List Q}
    (hw : Reduced w) (hlast : w = [] ∨ w.getLast? ≠ some q) : Reduced (w ++ [q]) := by
  unfold Reduced
  apply List.IsChain.append hw
  · exact List.isChain_singleton q
  · intro x hx y hy
    by_cases hw0 : w = []
    · have : w.getLast? = none := by simp [hw0]
      rw [this] at hx; simp at hx
    · have hlast' : w.getLast? ≠ some q := by
        rcases hlast with hw0' | hlast'
        · exact False.elim (hw0 hw0')
        · exact hlast'
      have hg := List.getLast?_eq_getLast hw0
      rw [hg] at hx; simp at hx; simp at hy
      rw [← hx, ← hy]
      intro hxq
      exact hlast' (by rw [hg, hxq])

private theorem reduced_dropLast {Q : Type uL} {w : List Q} (hw : Reduced w) :
    Reduced w.dropLast := by
  unfold Reduced; exact List.IsChain.dropLast hw

private theorem toggle_reduced {Q : Type uL} [DecidableEq Q] {q : Q} {w : List Q}
    (hw : Reduced w) : Reduced (toggle q w) := by
  by_cases hw0 : w = []
  · rw [hw0, toggle_empty]; unfold Reduced; exact List.isChain_singleton q
  · by_cases hlast : w.getLast? = some q
    · rw [toggle_last hw0 hlast]; exact reduced_dropLast hw
    · rw [toggle_not_last hw0 hlast]; exact reduced_append hw (Or.inr hlast)

private theorem dropLast_not_last {Q : Type uL} {q : Q} {w : List Q}
    (hw : Reduced w) (hw0 : w ≠ []) (hlast : w.getLast? = some q) :
    w.dropLast = [] ∨ w.dropLast.getLast? ≠ some q := by
  by_cases hd0 : w.dropLast = []
  · exact Or.inl hd0
  · right
    intro hdl
    have hg := List.getLast?_eq_getLast hw0
    rw [hg] at hlast
    have hgq : w.getLast hw0 = q := by simpa using hlast
    have hwdec : w.dropLast ++ [q] = w := by
      calc
        w.dropLast ++ [q] = w.dropLast ++ [w.getLast hw0] := by rw [← hgq]
        _ = w := List.dropLast_append_getLast hw0
    have hddec : w.dropLast = w.dropLast.dropLast ++ [w.dropLast.getLast hd0] :=
      (List.dropLast_append_getLast hd0).symm
    have hg2 := List.getLast?_eq_getLast hd0
    rw [hg2] at hdl
    have hdlast : w.dropLast.getLast hd0 = q := by simpa using hdl
    have hwqq : w = w.dropLast.dropLast ++ [q, q] := by
      calc
        w = w.dropLast ++ [q] := hwdec.symm
        _ = (w.dropLast.dropLast ++ [w.dropLast.getLast hd0]) ++ [q] := by
              exact (congrArg (fun z => z ++ [q]) hddec.symm).symm
        _ = (w.dropLast.dropLast ++ [q]) ++ [q] := by rw [hdlast]
        _ = w.dropLast.dropLast ++ [q, q] := by simp [List.append_assoc]
    unfold Reduced at hw
    rw [hwqq] at hw
    have hcc := (List.isChain_append.1 hw).2.1
    exact (List.IsChain.rel_head hcc) rfl

private theorem toggle_involutive {Q : Type uL} [DecidableEq Q] {q : Q} {w : List Q}
    (hw : Reduced w) : toggle q (toggle q w) = w := by
  by_cases hw0 : w = []
  · rw [hw0, toggle_empty]; simp [toggle]
  · by_cases hlast : w.getLast? = some q
    · rw [toggle_last hw0 hlast]
      have hd := dropLast_not_last hw hw0 hlast
      rw [toggle_push (q := q) (w := w.dropLast) hd]
      have hg := List.getLast?_eq_getLast hw0
      rw [hg] at hlast
      have hgq : w.getLast hw0 = q := by simpa using hlast
      calc
        w.dropLast ++ [q] = w.dropLast ++ [w.getLast hw0] := by rw [← hgq]
        _ = w := List.dropLast_append_getLast hw0
    · rw [toggle_not_last hw0 hlast]
      have h1 : w ++ [q] ≠ [] := by simp
      have h2 : (w ++ [q]).getLast? = some q := by
        simp [List.getLast?_append, Option.or]
      rw [toggle_last h1 h2]
      simp

/-- Surrounding a reducible word by equal letters keeps it reducible. -/
private theorem surround_reducesToEmpty {Letter : Type uL} {q : Letter} {X : List Letter}
    (h : ReducesToEmpty X) : ReducesToEmpty (q :: X ++ [q]) := by
  induction h with
  | nil =>
      simpa using ReducesToEmpty.insert ([] : List Letter) [] q ReducesToEmpty.nil
  | insert left right a reduced ih =>
      simpa [List.append_assoc] using
        (ReducesToEmpty.insert (q :: left) (right ++ [q]) a
          (by simpa [List.append_assoc] using ih))

/-- Moving the last letter of a reducible word to the front preserves
reducibility. -/
private theorem rotate_reducesToEmpty {Letter : Type uL} {q : Letter} {A : List Letter}
    (h : ReducesToEmpty (A ++ [q])) : ReducesToEmpty (q :: A) := by
  have helper : ∀ {large : List Letter}, ReducesToEmpty large →
      ∀ {A : List Letter} {q : Letter}, large = A ++ [q] →
        ReducesToEmpty (q :: A) := by
    intro large h
    induction h with
    | nil =>
        intro A q hEq
        have hlen : (0 : ℕ) = A.length + 1 := by
          simpa using congrArg List.length hEq.symm
        omega
    | insert left right a reduced ih =>
        intro A q hEq
        by_cases hright : right = []
        · subst right
          have hEq' : left ++ a :: a :: [] = A ++ [q] := by simpa using hEq
          have haq : a = q := by
            have hgA : (A ++ [q]).getLast? = some q := by simp
            have hgL : (left ++ a :: a :: []).getLast? = some a := by simp
            have hcon := congrArg (fun l => l.getLast?) hEq'
            change (left ++ [a, a]).getLast? = (A ++ [q]).getLast? at hcon
            rw [hgL, hgA] at hcon
            exact Option.some.inj hcon
          have hA : A = left ++ [a] := by
            have hdrop : (A ++ [q]).dropLast = (left ++ a :: a :: []).dropLast := by
              rw [hEq']
            have h1 : (A ++ [q]).dropLast = A := by
              rw [List.dropLast_append]; simp
            have h2 : (left ++ a :: a :: []).dropLast = left ++ [a] := by
              rw [List.dropLast_append]; simp
            rw [h1, h2] at hdrop
            exact hdrop
          subst q
          rw [hA]
          exact surround_reducesToEmpty (by simpa using reduced)
        · let right0 := right.dropLast
          have hright_last : right.getLast hright = q := by
            have hgl : (A ++ [q]).getLast? = some q := by simp
            have hgr : (left ++ a :: a :: right).getLast? = some (right.getLast hright) := by
              rw [List.getLast?_append]
              have hg2 : (a :: a :: right).getLast? = some (right.getLast hright) := by
                rw [List.getLast?_cons]
                rw [List.getLast?_cons]
                rw [List.getLast?_eq_getLast hright]
                simp
              rw [hg2]; simp
            have hcon := congrArg (fun l => l.getLast?) hEq
            change (left ++ a :: a :: right).getLast? = (A ++ [q]).getLast? at hcon
            rw [hgr, hgl] at hcon
            exact Option.some.inj hcon
          have hright_eq : right = right0 ++ [q] := by
            have hd := List.dropLast_append_getLast hright
            rw [← hd, hright_last]
          have hA : A = left ++ a :: a :: right0 := by
            have hdrop : (A ++ [q]).dropLast = (left ++ a :: a :: right).dropLast := by
              rw [hEq]
            have h1 : (A ++ [q]).dropLast = A := by
              rw [List.dropLast_append]; simp
            have h2 : (left ++ a :: a :: right).dropLast = left ++ a :: a :: right.dropLast := by
              simp [hright, List.dropLast_append, List.dropLast_cons_of_ne_nil]
            rw [h1, h2] at hdrop
            simpa [right0] using hdrop
          have hih := ih (A := left ++ right0) (q := q) (by
            rw [hright_eq]
            simp [List.append_assoc])
          rw [hA]
          simpa [List.append_assoc] using
            ReducesToEmpty.insert (q :: left) right0 a hih
  exact helper h rfl

/-- The right reduction of a word by toggles. -/
private def rightReduce {Q : Type uL} [DecidableEq Q] (word : List Q) : List Q :=
  word.foldr (fun q r => toggle q r) []

private theorem foldr_toggle_invariant {Q : Type uL} [DecidableEq Q] (word : List Q) :
    ReducesToEmpty (word ++ rightReduce word) := by
  induction word with
  | nil => exact ReducesToEmpty.nil
  | cons q rest ih =>
      let r := rightReduce rest
      have hr : ReducesToEmpty (rest ++ r) := by simpa [r] using ih
      by_cases hr0 : r = []
      · have hpush : toggle q r = r ++ [q] := toggle_push (Or.inl hr0)
        rw [rightReduce, List.foldr_cons]
        change ReducesToEmpty (q :: rest ++ toggle q r)
        rw [hpush]
        simpa [List.append_assoc, r] using surround_reducesToEmpty hr
      · by_cases hlast : r.getLast? = some q
        · have hpop : toggle q r = r.dropLast := toggle_last hr0 hlast
          rw [rightReduce, List.foldr_cons]
          change ReducesToEmpty (q :: rest ++ toggle q r)
          rw [hpop]
          have hdecomp : r = r.dropLast ++ [q] := by
            have hd := List.dropLast_append_getLast hr0
            have hg := List.getLast?_eq_getLast hr0
            rw [hg] at hlast
            have hgq : r.getLast hr0 = q := by simpa using hlast
            calc
              r = r.dropLast ++ [r.getLast hr0] := hd.symm
              _ = r.dropLast ++ [q] := by rw [hgq]
          have hrot := rotate_reducesToEmpty (A := rest ++ r.dropLast) (q := q) (by
            rw [hdecomp] at hr
            simpa [List.append_assoc] using hr)
          simpa [List.append_assoc, r] using hrot
        · have hpush : toggle q r = r ++ [q] := toggle_push (Or.inr hlast)
          rw [rightReduce, List.foldr_cons]
          change ReducesToEmpty (q :: rest ++ toggle q r)
          rw [hpush]
          simpa [List.append_assoc, r] using surround_reducesToEmpty hr

private def ReducedWord (Q : Type uL) := {w : List Q // Reduced w}

private def emptyWord (Q : Type uL) : ReducedWord Q :=
  ⟨[], by unfold Reduced; exact List.isChain_nil⟩

private def togglePerm {Q : Type uL} [DecidableEq Q] (q : Q) : Equiv.Perm (ReducedWord Q) where
  toFun w := ⟨toggle q w.1, toggle_reduced w.2⟩
  invFun w := ⟨toggle q w.1, toggle_reduced w.2⟩
  left_inv w := by
    apply Subtype.ext
    exact toggle_involutive w.2
  right_inv w := by
    apply Subtype.ext
    exact toggle_involutive w.2

def involutionRels (Q : Type uL) : Set (FreeGroup Q) :=
  {r | ∃ q : Q, r = FreeGroup.of q * FreeGroup.of q}

abbrev wordGroup (Q : Type uL) := PresentedGroup (involutionRels Q)

private def action {Q : Type uL} [DecidableEq Q] : FreeGroup Q →* Equiv.Perm (ReducedWord Q) :=
  FreeGroup.lift (fun q => togglePerm q)

private theorem action_of {Q : Type uL} [DecidableEq Q] (q : Q) :
    action (FreeGroup.of q) = togglePerm q := by
  simp [action]

private theorem action_sq {Q : Type uL} [DecidableEq Q] (q : Q) :
    action (FreeGroup.of q * FreeGroup.of q) = 1 := by
  apply Equiv.Perm.ext
  intro w
  change (action (FreeGroup.of q) * action (FreeGroup.of q)) w = w
  rw [action_of (q := q)]
  rw [Equiv.Perm.mul_apply]
  apply Subtype.ext
  exact toggle_involutive w.2

private def action'_ker_le {Q : Type uL} [DecidableEq Q] :
    Subgroup.normalClosure (involutionRels Q) ≤ action.ker := by
  exact Subgroup.normalClosure_le_normal (by
    intro r hr
    rcases hr with ⟨q, rfl⟩
    exact action.mem_ker.mpr (action_sq q))

private def action' {Q : Type uL} [DecidableEq Q] : wordGroup Q →* Equiv.Perm (ReducedWord Q) :=
  QuotientGroup.lift (Subgroup.normalClosure (involutionRels Q)) action action'_ker_le

private theorem action'_mk {Q : Type uL} [DecidableEq Q] (x : FreeGroup Q) :
    action' (PresentedGroup.mk (involutionRels Q) x) = action x := by
  change QuotientGroup.lift (Subgroup.normalClosure (involutionRels Q)) action action'_ker_le
    (QuotientGroup.mk x) = action x
  exact QuotientGroup.lift_mk (N := Subgroup.normalClosure (involutionRels Q))
    (φ := action) action'_ker_le x

private theorem rightReduce_reduced {Q : Type uL} [DecidableEq Q] (word : List Q) :
    Reduced (rightReduce word) := by
  induction word with
  | nil => unfold rightReduce; unfold Reduced; exact List.isChain_nil
  | cons q rest ih =>
      unfold rightReduce
      rw [List.foldr_cons]
      exact toggle_reduced ih

private theorem action'_prod {Q : Type uL} [DecidableEq Q] (word : List Q) :
    action' (PresentedGroup.mk (involutionRels Q) (word.map FreeGroup.of).prod) (emptyWord Q) =
      ⟨rightReduce word, rightReduce_reduced word⟩ := by
  induction word with
  | nil => simp [rightReduce, emptyWord, action'_mk]
  | cons q rest ih =>
      unfold rightReduce
      change action' (PresentedGroup.mk (involutionRels Q)
          (FreeGroup.of q * (rest.map FreeGroup.of).prod)) (emptyWord Q) =
        ⟨toggle q (List.foldr (fun q r => toggle q r) [] rest), rightReduce_reduced (q :: rest)⟩
      have hmul : (PresentedGroup.mk (involutionRels Q) (FreeGroup.of q *
          ((rest.map FreeGroup.of).prod))) =
          PresentedGroup.mk (involutionRels Q) (FreeGroup.of q) *
            PresentedGroup.mk (involutionRels Q) ((rest.map FreeGroup.of).prod) := by
        rw [map_mul]
      rw [hmul]
      rw [map_mul]
      rw [action'_mk, action_of (q := q)]
      rw [Equiv.Perm.mul_apply]
      rw [ih]
      rfl

theorem wordGroup_mk_prod_eq_one_iff_reducesToEmpty {Q : Type uL} [DecidableEq Q]
    (word : List Q) :
    (PresentedGroup.mk (involutionRels Q) (word.map FreeGroup.of).prod) = 1 ↔
      ReducesToEmpty word := by
  constructor
  · intro h
    have h' : action' (PresentedGroup.mk (involutionRels Q) (word.map FreeGroup.of).prod) = 1 := by
      rw [h]
      simp
    have happ := DFunLike.congr_fun h' (emptyWord Q)
    have hred := action'_prod word
    rw [hred] at happ
    have hrr : rightReduce word = [] := by
      have hsub := congrArg Subtype.val happ
      simpa [emptyWord] using hsub
    have hinv := foldr_toggle_invariant word
    simpa [hrr] using hinv
  · intro h
    induction h with
    | nil => simp
    | insert left right a reduced ih =>
        have hx : (PresentedGroup.mk (involutionRels Q)
            ((left ++ a :: a :: right).map FreeGroup.of).prod) =
            PresentedGroup.mk (involutionRels Q)
              (((left.map FreeGroup.of).prod) * (FreeGroup.of a * FreeGroup.of a) *
                (right.map FreeGroup.of).prod) := by
          congr 1
          simp [List.map_append, List.prod_append, mul_assoc]
        rw [hx]
        -- mk (x * (of a * of a) * y) = mk x * mk (of a * of a) * mk y = mk x * 1 * mk y
        rw [map_mul, map_mul]
        have hsq : PresentedGroup.mk (involutionRels Q) (FreeGroup.of a * FreeGroup.of a) = 1 := by
          exact PresentedGroup.one_of_mem ⟨a, rfl⟩
        rw [hsq]
        simp
        -- goal: mk ((left ++ right).map of).prod = 1 = ih
        have hconv : (PresentedGroup.mk (involutionRels Q)
            (((left.map FreeGroup.of).prod) * (right.map FreeGroup.of).prod)) =
            PresentedGroup.mk (involutionRels Q) ((left ++ right).map FreeGroup.of).prod := by
          congr 1
          simp [List.map_append, List.prod_append]
        rw [← map_mul]
        rw [hconv]
        exact ih

end InvolutionWord
namespace FiniteFourPlayerXORGame
variable (G : FiniteFourPlayerXORGame Question)

inductive Gen (Question : Type uQ) where
  | obs : Fin 4 → Question → Gen Question
  | J : Gen Question
deriving DecidableEq

/-- Relations of the base game group: observable involutions, cross-player
commutation, `J² = 1`, and centrality of `J`.  No clause equation occurs. -/
def baseRels (Question : Type uQ) : Set (FreeGroup (Gen Question)) :=
  {r |
    (∃ p q, r = FreeGroup.of (Gen.obs p q) * FreeGroup.of (Gen.obs p q)) ∨
    (∃ p p' q q', p ≠ p' ∧
      r = FreeGroup.of (Gen.obs p q) * FreeGroup.of (Gen.obs p' q') *
          (FreeGroup.of (Gen.obs p q))⁻¹ * (FreeGroup.of (Gen.obs p' q'))⁻¹) ∨
    (r = FreeGroup.of Gen.J * FreeGroup.of Gen.J) ∨
    (∃ p q, r = FreeGroup.of Gen.J * FreeGroup.of (Gen.obs p q) *
        (FreeGroup.of Gen.J)⁻¹ * (FreeGroup.of (Gen.obs p q))⁻¹) }

/-- The base game group, presented without clause relations. -/
abbrev baseGameGroup (Question : Type uQ) := PresentedGroup (baseRels Question)

/-- The canonical quotient map into the base game group. -/
abbrev baseMk (Question : Type uQ) : FreeGroup (Gen Question) →* baseGameGroup Question :=
  PresentedGroup.mk (baseRels Question)

/-- The observable of one player on one question in the base group. -/
def gameObservable (p : Fin 4) (q : Question) : baseGameGroup Question :=
  baseMk Question (FreeGroup.of (Gen.obs p q))

/-- The central involution of the base group. -/
def gameJ (Question : Type uQ) : baseGameGroup Question :=
  baseMk Question (FreeGroup.of Gen.J)

private theorem baseRels_obs_sq (p : Fin 4) (q : Question) :
    FreeGroup.of (Gen.obs p q) * FreeGroup.of (Gen.obs p q) ∈ baseRels Question := by
  unfold baseRels
  exact Or.inl ⟨p, q, rfl⟩

private theorem baseRels_cross (p p' : Fin 4) (hne : p ≠ p') (q q' : Question) :
    FreeGroup.of (Gen.obs p q) * FreeGroup.of (Gen.obs p' q') *
        (FreeGroup.of (Gen.obs p q))⁻¹ * (FreeGroup.of (Gen.obs p' q'))⁻¹ ∈
      baseRels Question := by
  unfold baseRels
  exact Or.inr (Or.inl ⟨p, p', q, q', hne, rfl⟩)

private theorem baseRels_J_sq : FreeGroup.of Gen.J * FreeGroup.of Gen.J ∈ baseRels Question := by
  unfold baseRels
  exact Or.inr (Or.inr (Or.inl rfl))

private theorem baseRels_J_central (p : Fin 4) (q : Question) :
    FreeGroup.of Gen.J * FreeGroup.of (Gen.obs p q) *
        (FreeGroup.of Gen.J)⁻¹ * (FreeGroup.of (Gen.obs p q))⁻¹ ∈
      baseRels Question := by
  unfold baseRels
  exact Or.inr (Or.inr (Or.inr ⟨p, q, rfl⟩))

/-- Observables square to the identity in the base group. -/
theorem gameObservable_sq (p : Fin 4) (q : Question) :
    gameObservable p q * gameObservable p q = 1 := by
  have hmk := PresentedGroup.one_of_mem (baseRels_obs_sq p q)
  simpa [gameObservable, baseMk, map_mul] using hmk

/-- Observables of distinct players commute in the base group. -/
theorem gameObservable_cross_commute {p p' : Fin 4} (hne : p ≠ p') (q q' : Question) :
    Commute (gameObservable p q) (gameObservable p' q') := by
  have hmk := PresentedGroup.one_of_mem (baseRels_cross p p' hne q q')
  have hmk' : gameObservable p q * gameObservable p' q' *
      (gameObservable p' q' * gameObservable p q)⁻¹ = 1 := by
    simpa [gameObservable, baseMk, map_mul, map_inv, mul_inv_rev] using hmk
  exact mul_inv_eq_one.mp hmk'

/-- `J` squares to the identity in the base group. -/
theorem gameJ_sq : gameJ Question * gameJ Question = 1 := by
  change (baseMk Question (FreeGroup.of Gen.J)) * (baseMk Question (FreeGroup.of Gen.J)) = 1
  rw [← map_mul]
  exact PresentedGroup.one_of_mem baseRels_J_sq

private theorem gameJ_commutes_generator (g : Gen Question) :
    Commute (gameJ Question) (PresentedGroup.of g) := by
  cases g with
  | obs p q =>
      have hmk := PresentedGroup.one_of_mem (baseRels_J_central p q)
      have hmk' : gameJ Question * gameObservable p q *
          (gameObservable p q * gameJ Question)⁻¹ = 1 := by
        simpa [gameJ, gameObservable, baseMk, map_mul, map_inv, mul_inv_rev] using hmk
      have heq : gameJ Question * gameObservable p q = gameObservable p q * gameJ Question :=
        mul_inv_eq_one.mp hmk'
      exact heq
  | J =>
      change gameJ Question * gameJ Question = gameJ Question * gameJ Question
      rfl

/-- `J` is central in the base group. -/
theorem gameJ_central (x : baseGameGroup Question) : Commute (gameJ Question) x := by
  have hx : x ∈ Subgroup.closure (Set.range (PresentedGroup.of : Gen Question → baseGameGroup Question)) := by
    rw [PresentedGroup.closure_range_of (baseRels Question)]
    trivial
  refine Subgroup.closure_induction (p := fun y _ => Commute (gameJ Question) y) ?mem ?one ?mul ?inv hx
  · intro y hy
    rcases hy with ⟨g, rfl⟩
    exact gameJ_commutes_generator g
  · simpa [Commute]
  · intro x y hx hy hcx hcy
    exact hcx.mul_right hcy
  · intro x hx hcx
    exact hcx.inv_right

def signOn (Question : Type uQ) (g : Gen Question) : Multiplicative (ZMod 2) :=
  match g with
  | Gen.obs p q => 1
  | Gen.J => Multiplicative.ofAdd (1 : ZMod 2)

@[simp] theorem signOn_obs (Question : Type uQ) (p : Fin 4) (q : Question) :
    signOn Question (Gen.obs p q) = 1 := rfl

@[simp] theorem signOn_J (Question : Type uQ) :
    signOn Question Gen.J = Multiplicative.ofAdd (1 : ZMod 2) := rfl

theorem signKer_le (Question : Type uQ) :
    Subgroup.normalClosure (baseRels Question) ≤
      (FreeGroup.lift (signOn Question)).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  rcases hr with ⟨p, q, rfl⟩ | ⟨p, p', q, q', hne, rfl⟩ | rfl | ⟨p, q, rfl⟩
  · simp [signOn]
  · simp [signOn]
  · -- J² = 1
    change Multiplicative.ofAdd ((1 : ZMod 2) + 1) = 1
    have h : (1 + 1 : ZMod 2) = 0 := by
      norm_num
      exact ZMod.natCast_self 2
    rw [h]
    rfl
  · simp [signOn]

/-- The sign homomorphism sending every observable to zero and `J` to one. -/
def signProjection (Question : Type uQ) : baseGameGroup Question →* Multiplicative (ZMod 2) :=
  QuotientGroup.lift (Subgroup.normalClosure (baseRels Question))
    (FreeGroup.lift (signOn Question)) (signKer_le Question)

@[simp] theorem signProjection_mk (x : FreeGroup (Gen Question)) :
    signProjection Question (baseMk Question x) = (FreeGroup.lift (signOn Question)) x := by
  change (QuotientGroup.lift (Subgroup.normalClosure (baseRels Question))
      (FreeGroup.lift (signOn Question)) (signKer_le Question)) (QuotientGroup.mk x) =
    (FreeGroup.lift (signOn Question)) x
  exact QuotientGroup.lift_mk (N := Subgroup.normalClosure (baseRels Question))
    (φ := FreeGroup.lift (signOn Question)) (signKer_le Question) x

@[simp] theorem signProjection_gameJ : signProjection Question (gameJ Question) =
    Multiplicative.ofAdd (1 : ZMod 2) := by
  simp [gameJ, baseMk, signOn]

@[simp] theorem signProjection_gameObservable (p : Fin 4) (q : Question) :
    signProjection Question (gameObservable p q) = 1 := by
  simp [gameObservable, baseMk, signOn]

def playerOn (p : Fin 4) (Question : Type uQ) (g : Gen Question) :
    InvolutionWord.wordGroup Question :=
  match g with
  | Gen.obs p' q => if p' = p then
        PresentedGroup.mk (InvolutionWord.involutionRels Question) (FreeGroup.of q) else 1
  | Gen.J => 1

@[simp] theorem playerOn_self (p : Fin 4) (Question : Type uQ) (q : Question) :
    playerOn p Question (Gen.obs p q) =
      PresentedGroup.mk (InvolutionWord.involutionRels Question) (FreeGroup.of q) := by
  simp [playerOn]

@[simp] theorem playerOn_other {p p' : Fin 4} (hne : p ≠ p') (Question : Type uQ)
    (q : Question) : playerOn p Question (Gen.obs p' q) = 1 := by
  simp [playerOn, hne, hne.symm]

@[simp] theorem playerOn_J (p : Fin 4) (Question : Type uQ) :
    playerOn p Question Gen.J = 1 := rfl

theorem playerKer_le (p : Fin 4) (Question : Type uQ) :
    Subgroup.normalClosure (baseRels Question) ≤
      (FreeGroup.lift (playerOn p Question)).ker := by
  apply Subgroup.normalClosure_le_normal
  intro r hr
  rcases hr with ⟨p', q, rfl⟩ | ⟨p₁, p₂, q₁, q₂, hne, rfl⟩ | rfl | ⟨p', q, rfl⟩
  · by_cases h : p' = p
    · subst p'
      have hmk := PresentedGroup.one_of_mem (rels := InvolutionWord.involutionRels Question)
        (x := FreeGroup.of q * FreeGroup.of q) ⟨q, rfl⟩
      simpa [playerOn, map_mul] using hmk
    · simp [playerOn, h]
  · by_cases h1 : p₁ = p
    · have h2 : p₂ ≠ p := by
        intro h2
        exact hne (h1.trans h2.symm)
      simp [playerOn, h1, h2]
    · simp [playerOn, h1]
  · simp [playerOn]
  · simp [playerOn]

/-- The per-player projection onto the involution word group. -/
def playerProjection (p : Fin 4) (Question : Type uQ) :
    baseGameGroup Question →* InvolutionWord.wordGroup Question :=
  QuotientGroup.lift (Subgroup.normalClosure (baseRels Question))
    (FreeGroup.lift (playerOn p Question)) (playerKer_le p Question)

@[simp] theorem playerProjection_mk (p : Fin 4) (x : FreeGroup (Gen Question)) :
    playerProjection p Question (baseMk Question x) =
      (FreeGroup.lift (playerOn p Question)) x := by
  change (QuotientGroup.lift (Subgroup.normalClosure (baseRels Question))
      (FreeGroup.lift (playerOn p Question)) (playerKer_le p Question)) (QuotientGroup.mk x) =
    (FreeGroup.lift (playerOn p Question)) x
  exact QuotientGroup.lift_mk (N := Subgroup.normalClosure (baseRels Question))
    (φ := FreeGroup.lift (playerOn p Question)) (playerKer_le p Question) x

@[simp] theorem playerProjection_gameJ (p : Fin 4) :
    playerProjection p Question (gameJ Question) = 1 := by
  simp [gameJ, baseMk, playerOn]

@[simp] theorem playerProjection_gameObservable_self (p : Fin 4) (q : Question) :
    playerProjection p Question (gameObservable p q) =
      PresentedGroup.mk (InvolutionWord.involutionRels Question) (FreeGroup.of q) := by
  simp [gameObservable, baseMk, playerOn]

@[simp] theorem playerProjection_gameObservable_other {p p' : Fin 4} (hne : p ≠ p')
    (q : Question) : playerProjection p Question (gameObservable p' q) = 1 := by
  simp [gameObservable, baseMk, playerOn, hne, hne.symm]

/-- The observable part of a clause: the product of the four player
observables. -/
def clauseObservablePart (G : FiniteFourPlayerXORGame Question) (c : G.ReducedClauseId) :
    baseGameGroup Question :=
  List.prod ((List.finRange 4).map (fun p => gameObservable p (G.reducedQuery c p)))

/-- The signed clause element inside the base group. -/
def clauseElement (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    baseGameGroup Question :=
  clauseObservablePart G c * gameJ Question ^ (G.reducedSign hconflict c).val

/-- The ordinary (generally nonnormal) subgroup generated by the clause
elements. -/
def clauseSubgroup (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : Subgroup (baseGameGroup Question) :=
  Subgroup.closure (Set.range (clauseElement G hconflict))

private theorem comm_prod_left {M : Type uM} [Monoid M] {a : M} (l : List M)
    (h : ∀ y ∈ l, Commute a y) : a * l.prod = l.prod * a := by
  induction l with
  | nil => simp
  | cons b rest ih =>
      calc
        a * (b * rest.prod) = (a * b) * rest.prod := by rw [mul_assoc]
        _ = (b * a) * rest.prod := by rw [(h b (by simp)).eq]
        _ = b * (a * rest.prod) := by rw [← mul_assoc]
        _ = b * (rest.prod * a) := by rw [ih (by intro y hy; exact h y (by simp [hy]))]
        _ = (b * rest.prod) * a := by rw [← mul_assoc]

private theorem map_list_prod {M : Type uM} {N : Type uN} [Monoid M] [Monoid N]
    (f : M →* N) (l : List M) : f l.prod = (l.map f).prod := by
  induction l with
  | nil => simp
  | cons a rest ih => simp [ih]

private theorem finRange4_prod_mul {M : Type uM} [Group M]
    (x r : Fin 4 → M)
    (hxr : ∀ {p p' : Fin 4}, p ≠ p' → Commute (x p) (r p'))
    (hxx : ∀ {p p' : Fin 4}, p ≠ p' → Commute (x p) (x p')) :
    ((List.finRange 4).map (fun p => x p * r p)).prod =
      ((List.finRange 4).map x).prod * ((List.finRange 4).map r).prod := by
  norm_num [List.finRange]
  have h1 : Commute (x 1) (r 0) := hxr (by decide : (1 : Fin 4) ≠ 0)
  have h2 : Commute (x 2) (r 0) := hxr (by decide : (2 : Fin 4) ≠ 0)
  have h3 : Commute (x 2) (r 1) := hxr (by decide : (2 : Fin 4) ≠ 1)
  have h4 : Commute (x 3) (r 0) := hxr (by decide : (3 : Fin 4) ≠ 0)
  have h5 : Commute (x 3) (r 1) := hxr (by decide : (3 : Fin 4) ≠ 1)
  have h6 : Commute (x 3) (r 2) := hxr (by decide : (3 : Fin 4) ≠ 2)
  have h01 : (x 0 * r 0) * (x 1 * r 1) = (x 0 * x 1) * (r 0 * r 1) := by
    calc
      (x 0 * r 0) * (x 1 * r 1) = x 0 * (r 0 * (x 1 * r 1)) := by group
      _ = x 0 * ((r 0 * x 1) * r 1) := by rw [mul_assoc]
      _ = x 0 * ((x 1 * r 0) * r 1) := by rw [h1.eq]
      _ = x 0 * (x 1 * (r 0 * r 1)) := by rw [mul_assoc]
      _ = (x 0 * x 1) * (r 0 * r 1) := by group
  have h23 : (x 2 * r 2) * (x 3 * r 3) = (x 2 * x 3) * (r 2 * r 3) := by
    calc
      (x 2 * r 2) * (x 3 * r 3) = x 2 * (r 2 * (x 3 * r 3)) := by group
      _ = x 2 * ((r 2 * x 3) * r 3) := by rw [mul_assoc]
      _ = x 2 * ((x 3 * r 2) * r 3) := by rw [h6.eq]
      _ = x 2 * (x 3 * (r 2 * r 3)) := by rw [mul_assoc]
      _ = (x 2 * x 3) * (r 2 * r 3) := by group
  have hB1A2 : (r 0 * r 1) * (x 2 * x 3) = (x 2 * x 3) * (r 0 * r 1) := by
    have hc1 : Commute (x 2 * x 3) (r 1) := Commute.mul_left h3 h5
    have hc2 : Commute (x 2 * x 3) (r 0) := Commute.mul_left h2 h4
    calc
      (r 0 * r 1) * (x 2 * x 3) = r 0 * (r 1 * (x 2 * x 3)) := by rw [mul_assoc]
      _ = r 0 * ((x 2 * x 3) * r 1) := by rw [hc1.symm.eq]
      _ = (r 0 * (x 2 * x 3)) * r 1 := by rw [← mul_assoc]
      _ = ((x 2 * x 3) * r 0) * r 1 := by rw [hc2.symm.eq]
      _ = (x 2 * x 3) * (r 0 * r 1) := by rw [mul_assoc]
  calc
    x 0 * r 0 * (x 1 * r 1 * (x 2 * r 2 * (x 3 * r 3)))
        = (((x 0 * r 0) * (x 1 * r 1)) * (x 2 * r 2)) * (x 3 * r 3) := by group
    _ = ((x 0 * r 0) * (x 1 * r 1)) * ((x 2 * r 2) * (x 3 * r 3)) := by group
    _ = ((x 0 * x 1) * (r 0 * r 1)) * ((x 2 * x 3) * (r 2 * r 3)) := by
          rw [h01, h23]
    _ = ((x 0 * x 1) * (x 2 * x 3)) * ((r 0 * r 1) * (r 2 * r 3)) := by
          calc
            ((x 0 * x 1) * (r 0 * r 1)) * ((x 2 * x 3) * (r 2 * r 3))
                = (x 0 * x 1) * ((r 0 * r 1) * ((x 2 * x 3) * (r 2 * r 3))) := by group
            _ = (x 0 * x 1) * (((r 0 * r 1) * (x 2 * x 3)) * (r 2 * r 3)) := by
                  have hm : (r 0 * r 1) * ((x 2 * x 3) * (r 2 * r 3)) =
                      ((r 0 * r 1) * (x 2 * x 3)) * (r 2 * r 3) := by rw [← mul_assoc]
                  rw [hm]
            _ = (x 0 * x 1) * (((x 2 * x 3) * (r 0 * r 1)) * (r 2 * r 3)) := by
                  rw [hB1A2]
            _ = (x 0 * x 1) * ((x 2 * x 3) * ((r 0 * r 1) * (r 2 * r 3))) := by
                  have hm : ((x 2 * x 3) * (r 0 * r 1)) * (r 2 * r 3) =
                      (x 2 * x 3) * ((r 0 * r 1) * (r 2 * r 3)) := by rw [mul_assoc]
                  rw [hm]
            _ = ((x 0 * x 1) * (x 2 * x 3)) * ((r 0 * r 1) * (r 2 * r 3)) := by group
    _ = (x 0 * (x 1 * (x 2 * x 3))) * (r 0 * (r 1 * (r 2 * r 3))) := by group

private theorem finRange_pairwise_commute {M : Type uM} [Monoid M]
    (obs : Fin 4 → M) (hcomm : ∀ {p p' : Fin 4}, p ≠ p' → Commute (obs p) (obs p')) :
    ((List.finRange 4).map obs).Pairwise (fun a b => Commute a b) := by
  norm_num [List.finRange]
  constructor
  · constructor
    · exact hcomm (by decide : (0 : Fin 4) ≠ 1)
    · constructor
      · exact hcomm (by decide : (0 : Fin 4) ≠ 2)
      · exact hcomm (by decide : (0 : Fin 4) ≠ 3)
  · constructor
    · constructor
      · exact hcomm (by decide : (1 : Fin 4) ≠ 2)
      · exact hcomm (by decide : (1 : Fin 4) ≠ 3)
    · exact hcomm (by decide : (2 : Fin 4) ≠ 3)

private theorem list_prod_sq_of_pairwise_commute {M : Type uM} [Monoid M]
    (l : List M) (hsq : ∀ a ∈ l, a * a = 1)
    (hcomm : l.Pairwise (fun a b => Commute a b)) :
    l.prod * l.prod = 1 := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      match hcomm with
      | .cons hhead htail =>
          have hc : Commute a rest.prod := by
            exact comm_prod_left rest (by
              intro y hy
              exact hhead y (by simp [hy]))
          calc
            (a :: rest).prod * (a :: rest).prod
                = (a * rest.prod) * (a * rest.prod) := rfl
            _ = a * (rest.prod * (a * rest.prod)) := by rw [mul_assoc]
            _ = a * ((rest.prod * a) * rest.prod) := by rw [mul_assoc]
            _ = a * ((a * rest.prod) * rest.prod) := by rw [hc.eq.symm]
            _ = (a * (a * rest.prod)) * rest.prod := by rw [← mul_assoc]
            _ = ((a * a) * rest.prod) * rest.prod := by rw [← mul_assoc]
            _ = (1 * rest.prod) * rest.prod := by rw [hsq a (by simp)]
            _ = rest.prod * rest.prod := by simp
            _ = 1 := ih (by intro y hy; exact hsq y (by simp [hy])) htail

theorem clauseObservablePart_sq (c : G.ReducedClauseId) :
    clauseObservablePart G c * clauseObservablePart G c = 1 := by
  unfold clauseObservablePart
  exact list_prod_sq_of_pairwise_commute
    ((List.finRange 4).map (fun p => gameObservable p (G.reducedQuery c p)))
    (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      exact gameObservable_sq p (G.reducedQuery c p))
    (finRange_pairwise_commute (fun p => gameObservable p (G.reducedQuery c p))
      (by intro p p' hne; exact gameObservable_cross_commute hne _ _))

theorem gameJ_pow_central (n : ℕ) (x : baseGameGroup Question) :
    Commute (gameJ Question ^ n) x := by
  exact (gameJ_central x).pow_left n

theorem clauseElement_sq (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    clauseElement G hconflict c * clauseElement G hconflict c = 1 := by
  unfold clauseElement
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (G.reducedSign hconflict c) with hs | hs
  · have hs' : (G.reducedSign hconflict c).val = 0 := by
      simp [hs]
    simp [hs', clauseObservablePart_sq]
  · have hs' : (G.reducedSign hconflict c).val = 1 := by
      rw [hs]
      change (1 : Fin 2).val = 1
      rfl
    have hpow : gameJ Question ^ (G.reducedSign hconflict c).val = gameJ Question := by
      rw [hs']
      simp
    have hc : Commute (clauseObservablePart G c) (gameJ Question) :=
      (gameJ_central (clauseObservablePart G c)).symm
    calc
      clauseElement G hconflict c * clauseElement G hconflict c
          = (clauseObservablePart G c * gameJ Question ^ (G.reducedSign hconflict c).val) *
              (clauseObservablePart G c * gameJ Question ^ (G.reducedSign hconflict c).val) := by
              rfl
      _ = (clauseObservablePart G c * gameJ Question) *
              (clauseObservablePart G c * gameJ Question) := by
              rw [hpow]
      _ = clauseObservablePart G c * ((gameJ Question * clauseObservablePart G c) * gameJ Question) := by
              group
      _ = clauseObservablePart G c * ((clauseObservablePart G c * gameJ Question) * gameJ Question) := by
              rw [hc.eq]
      _ = (clauseObservablePart G c * clauseObservablePart G c) * (gameJ Question * gameJ Question) := by
              group
      _ = 1 := by rw [clauseObservablePart_sq, gameJ_sq]; simp

theorem clauseElement_inv (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    (clauseElement G hconflict c)⁻¹ = clauseElement G hconflict c := by
  have hx := clauseElement_sq G hconflict c
  calc
    (clauseElement G hconflict c)⁻¹
        = (clauseElement G hconflict c)⁻¹ * 1 := by rw [mul_one]
    _ = (clauseElement G hconflict c)⁻¹ *
          (clauseElement G hconflict c * clauseElement G hconflict c) := by rw [hx]
    _ = ((clauseElement G hconflict c)⁻¹ * clauseElement G hconflict c) *
          clauseElement G hconflict c := by rw [← mul_assoc]
    _ = 1 * clauseElement G hconflict c := by rw [inv_mul_cancel]
    _ = clauseElement G hconflict c := by rw [one_mul]

private theorem clauseElement_word_mem (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (word : List G.ReducedClauseId) :
    (word.map (G.clauseElement hconflict)).prod ∈ G.clauseSubgroup hconflict := by
  induction word with
  | nil => simpa using (G.clauseSubgroup hconflict).one_mem
  | cons c rest ih =>
      have hmem : G.clauseElement hconflict c ∈ Set.range (G.clauseElement hconflict) :=
        ⟨c, rfl⟩
      exact (G.clauseSubgroup hconflict).mul_mem (Subgroup.subset_closure hmem) ih

theorem mem_clauseSubgroup_iff_exists_list_product
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (x : baseGameGroup Question) :
    x ∈ G.clauseSubgroup hconflict ↔
      ∃ word : List G.ReducedClauseId,
        (word.map (G.clauseElement hconflict)).prod = x := by
  constructor
  · intro hx
    refine Subgroup.closure_induction (p := fun y _ =>
        ∃ word : List G.ReducedClauseId, (word.map (G.clauseElement hconflict)).prod = y) ?_ ?_ ?_ ?_ hx
    · intro y hy
      rcases hy with ⟨c, rfl⟩
      exact ⟨[c], by simp⟩
    · exact ⟨[], by simp⟩
    · intro x y hx hy ⟨wx, hwx⟩ ⟨wy, hwy⟩
      refine ⟨wx ++ wy, ?_⟩
      rw [List.map_append, List.prod_append, hwx, hwy]
    · intro x hx ⟨wx, hwx⟩
      refine ⟨wx.reverse, ?_⟩
      have hmap : (List.map (fun y : baseGameGroup Question => y⁻¹)
            (List.map (G.clauseElement hconflict) wx)) =
          List.map (G.clauseElement hconflict) wx := by
        rw [List.map_map]
        apply List.map_congr_left
        intro y hy
        change (G.clauseElement hconflict y)⁻¹ = G.clauseElement hconflict y
        exact G.clauseElement_inv hconflict y
      have hm : (wx.reverse.map (G.clauseElement hconflict)).prod =
          (wx.map (G.clauseElement hconflict)).prod⁻¹ := by
        rw [List.map_reverse, List.prod_reverse_noncomm]
        rw [hmap]
      rw [hm]
      exact congrArg (fun z : baseGameGroup Question => z⁻¹) hwx
  · rintro ⟨word, hx⟩
    rw [← hx]
    exact clauseElement_word_mem G hconflict word

theorem clauseElement_word_product_eq
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (word : List G.ReducedClauseId) :
    (word.map (G.clauseElement hconflict)).prod =
      (word.map (fun c => G.clauseObservablePart c)).prod *
        gameJ Question ^ (word.map (fun c => (G.reducedSign hconflict c).val)).sum := by
  induction word with
  | nil => simp
  | cons c rest ih =>
      let s : ℕ := (G.reducedSign hconflict c).val
      let t : ℕ := (rest.map (fun c => (G.reducedSign hconflict c).val)).sum
      calc
        ((c :: rest).map (G.clauseElement hconflict)).prod
            = G.clauseElement hconflict c * (rest.map (G.clauseElement hconflict)).prod := by
                simp
        _ = (G.clauseObservablePart c * gameJ Question ^ s) *
              ((rest.map (fun c => G.clauseObservablePart c)).prod * gameJ Question ^ t) := by
                rw [ih]
                rfl
        _ = G.clauseObservablePart c *
              (gameJ Question ^ s * (rest.map (fun c => G.clauseObservablePart c)).prod) *
              gameJ Question ^ t := by
                group
        _ = G.clauseObservablePart c *
              ((rest.map (fun c => G.clauseObservablePart c)).prod * gameJ Question ^ s) *
              gameJ Question ^ t := by
                rw [(gameJ_pow_central s _).eq]
        _ = (G.clauseObservablePart c * (rest.map (fun c => G.clauseObservablePart c)).prod) *
              (gameJ Question ^ s * gameJ Question ^ t) := by
                group
        _ = (G.clauseObservablePart c * (rest.map (fun c => G.clauseObservablePart c)).prod) *
              gameJ Question ^ (s + t) := by
                rw [pow_add]
        _ = (G.clauseObservablePart c * (rest.map (fun c => G.clauseObservablePart c)).prod) *
              gameJ Question ^ (((c :: rest).map (fun c => (G.reducedSign hconflict c).val)).sum) := by
                simp [s, t]
        _ = ((c :: rest).map (fun c => G.clauseObservablePart c)).prod *
              gameJ Question ^ (((c :: rest).map (fun c => (G.reducedSign hconflict c).val)).sum) := by
                simp

private theorem gameObservable_prod_commute {p p' : Fin 4} (hne : p ≠ p')
    (q : Question) (l : List Question) :
    Commute (gameObservable p q)
      (List.prod (l.map (fun q' => gameObservable p' q'))) := by
  exact comm_prod_left (l.map (fun q' => gameObservable p' q')) (by
    intro y hy
    rcases List.mem_map.mp hy with ⟨q', hq', rfl⟩
    exact gameObservable_cross_commute hne q q')

theorem clauseObservablePart_word_regroup
    (G : FiniteFourPlayerXORGame Question) (word : List G.ReducedClauseId) :
    (word.map (fun c => G.clauseObservablePart c)).prod =
      List.prod ((List.finRange 4).map (fun p =>
        (word.map (fun c => gameObservable p (G.reducedQuery c p))).prod)) := by
  induction word with
  | nil => simp [clauseObservablePart]
  | cons c rest ih =>
      calc
        ((c :: rest).map (fun c => G.clauseObservablePart c)).prod
            = G.clauseObservablePart c * (rest.map (fun c => G.clauseObservablePart c)).prod := by
                simp
        _ = List.prod ((List.finRange 4).map (fun p => gameObservable p (G.reducedQuery c p))) *
              List.prod ((List.finRange 4).map (fun p =>
                (rest.map (fun c' => gameObservable p (G.reducedQuery c' p))).prod)) := by
                rw [clauseObservablePart, ih]
        _ = List.prod ((List.finRange 4).map (fun p =>
              gameObservable p (G.reducedQuery c p) *
                (rest.map (fun c' => gameObservable p (G.reducedQuery c' p))).prod)) := by
              -- apply finRange4_prod_mul in reverse
              symm
              apply finRange4_prod_mul
              · intro p p' hne
                simpa [List.map_map, Function.comp_def] using
                  gameObservable_prod_commute hne (G.reducedQuery c p)
                    (rest.map (fun c' => G.reducedQuery c' p'))
              · intro p p' hne
                exact gameObservable_cross_commute hne (G.reducedQuery c p) (G.reducedQuery c p')
        _ = List.prod ((List.finRange 4).map (fun p =>
              ((c :: rest).map (fun c' => gameObservable p (G.reducedQuery c' p))).prod)) := by
              apply congrArg List.prod
              apply List.map_congr_left
              intro p hp
              simp

/-- The per-player embedding of the involution word group into the base game
group. -/
def pageEmbedding (p : Fin 4) :
    InvolutionWord.wordGroup Question →* baseGameGroup Question :=
  QuotientGroup.lift (Subgroup.normalClosure (InvolutionWord.involutionRels Question))
    (FreeGroup.lift (fun q : Question => gameObservable p q))
    (by
      apply Subgroup.normalClosure_le_normal
      intro r hr
      rcases hr with ⟨q, rfl⟩
      simpa [map_mul] using gameObservable_sq p q)

@[simp] theorem pageEmbedding_mk_of (p : Fin 4) (q : Question) :
    pageEmbedding p
        (PresentedGroup.mk (InvolutionWord.involutionRels Question) (FreeGroup.of q)) =
      gameObservable p q := by
  change (QuotientGroup.lift (Subgroup.normalClosure (InvolutionWord.involutionRels Question))
      (FreeGroup.lift (fun q : Question => gameObservable p q)) _) (QuotientGroup.mk (FreeGroup.of q)) =
    gameObservable p q
  rw [QuotientGroup.lift_mk]
  simp

theorem pageEmbedding_mk_prod (p : Fin 4) (word : List Question) :
    pageEmbedding p
        (PresentedGroup.mk (InvolutionWord.involutionRels Question)
          (word.map FreeGroup.of).prod) =
      List.prod (word.map (fun q => gameObservable p q)) := by
  induction word with
  | nil => simp
  | cons q rest ih =>
      simp [map_mul, map_list_prod, Function.comp_def, pageEmbedding_mk_of, ih]

private theorem pow_two_eq_one_pow_mod {M : Type uM} [Monoid M] {a : M}
    (h : a * a = 1) (n : ℕ) : a ^ n = a ^ (n % 2) := by
  have hpow2 : a ^ 2 = 1 := by
    simpa [pow_two] using h
  rcases Nat.mod_two_eq_zero_or_one n with hn | hn
  · have hdiv : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
    have hn' : n = 2 * (n / 2) := by
      have hdiv' : 0 + 2 * (n / 2) = n := by simpa [hn] using hdiv
      omega
    calc
      a ^ n = a ^ (2 * (n / 2)) := by rw [← hn']
      _ = (a ^ 2) ^ (n / 2) := by rw [pow_mul]
      _ = 1 ^ (n / 2) := by rw [hpow2]
      _ = 1 := by simp
      _ = a ^ (n % 2) := by rw [hn]; simp
  · have hdiv : n % 2 + 2 * (n / 2) = n := Nat.mod_add_div n 2
    have hn' : n = 2 * (n / 2) + 1 := by
      have hdiv' : 1 + 2 * (n / 2) = n := by simpa [hn] using hdiv
      omega
    calc
      a ^ n = a ^ (2 * (n / 2) + 1) := by rw [← hn']
      _ = a ^ (2 * (n / 2)) * a := by rw [pow_succ]
      _ = (a ^ 2) ^ (n / 2) * a := by rw [pow_mul]
      _ = 1 ^ (n / 2) * a := by rw [hpow2]
      _ = a := by simp
      _ = a ^ (n % 2) := by rw [hn]; simp

private theorem ofAdd_sum_prod (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (word : List G.ReducedClauseId) :
    (word.map (fun c => Multiplicative.ofAdd (G.reducedSign hconflict c))).prod =
      Multiplicative.ofAdd ((word.map (G.reducedSign hconflict)).sum) := by
  induction word with
  | nil => simp
  | cons c rest ih => simp [ih]

private theorem zmod_sum_natCast (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (word : List G.ReducedClauseId) :
    ((word.map (fun c => (G.reducedSign hconflict c).val)).sum : ZMod 2) =
      (word.map (G.reducedSign hconflict)).sum := by
  induction word with
  | nil => simp
  | cons c rest ih =>
      rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
      change (((G.reducedSign hconflict c).val +
          (rest.map (fun c' => (G.reducedSign hconflict c').val)).sum : ℕ) : ZMod 2) =
        G.reducedSign hconflict c + (rest.map (G.reducedSign hconflict)).sum
      rw [Nat.cast_add, ih]
      congr 1
      exact ZMod.natCast_zmod_val (G.reducedSign hconflict c)

theorem signProjection_clauseElement (hconflict : ¬ G.HasConflictingTargets)
    (c : G.ReducedClauseId) :
    signProjection Question (G.clauseElement hconflict c) =
      Multiplicative.ofAdd (G.reducedSign hconflict c) := by
  unfold clauseElement clauseObservablePart
  rw [map_mul, map_pow]
  have hP : signProjection Question
      (List.prod ((List.finRange 4).map (fun p => gameObservable p (G.reducedQuery c p)))) = 1 := by
    rw [map_list_prod]
    simp [Function.comp_def]
  rw [hP, signProjection_gameJ, one_mul]
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (G.reducedSign hconflict c) with hs0 | hs1
  · rw [hs0]
    simp
  · rw [hs1]
    have hval : (1 : ZMod 2).val = 1 := by
      change (1 : Fin 2).val = 1
      rfl
    rw [hval]
    simp

theorem playerProjection_clauseElement (p : Fin 4)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    playerProjection p Question (G.clauseElement hconflict c) =
      PresentedGroup.mk (InvolutionWord.involutionRels Question) (FreeGroup.of (G.reducedQuery c p)) := by
  unfold clauseElement clauseObservablePart
  rw [map_mul, map_pow, playerProjection_gameJ]
  simp
  rw [map_list_prod]
  simp [gameObservable, baseMk, playerProjection_mk, playerOn]
  fin_cases p <;> simp [List.finRange, playerOn]

theorem gameJ_mem_clauseSubgroup_iff_hasOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    gameJ Question ∈ G.clauseSubgroup hconflict ↔
      HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  constructor
  · intro hm
    rcases (mem_clauseSubgroup_iff_exists_list_product G hconflict (gameJ Question)).mp hm with
      ⟨word, hw⟩
    have hsign' : (word.map (G.reducedSign hconflict)).sum = 1 := by
      have hsign := congrArg (signProjection Question) hw
      rw [map_list_prod] at hsign
      rw [List.map_map, Function.comp_def] at hsign
      simp [signProjection_clauseElement] at hsign
      rw [ofAdd_sum_prod G hconflict word] at hsign
      exact (Multiplicative.ofAdd.injective hsign)
    have hbal : ∀ p : Fin 4, InvolutionWord.ReducesToEmpty
        (word.map (fun c => G.reducedQuery c p)) := by
      intro p
      have hp := congrArg (playerProjection p Question) hw
      rw [map_list_prod] at hp
      rw [List.map_map, Function.comp_def] at hp
      simp [playerProjection_clauseElement] at hp
      have hm : PresentedGroup.mk (InvolutionWord.involutionRels Question)
          ((word.map (fun c => G.reducedQuery c p)).map FreeGroup.of).prod = 1 := by
        rw [map_list_prod]
        simpa [List.map_map, Function.comp_def] using hp
      exact (InvolutionWord.wordGroup_mk_prod_eq_one_iff_reducesToEmpty
        (word.map (fun c => G.reducedQuery c p))).mp hm
    exact ⟨word, ⟨hbal, by
      rw [parityPairing_occurrenceParity]
      exact hsign'⟩⟩
  · rintro ⟨word, hbal, hodd⟩
    have hsign : (word.map (G.reducedSign hconflict)).sum = 1 := by
      rw [← parityPairing_occurrenceParity]
      exact hodd
    let N : ℕ := (word.map (fun c => (G.reducedSign hconflict c).val)).sum
    have hN : (N : ZMod 2) = 1 := by
      rw [zmod_sum_natCast G hconflict word]
      exact hsign
    have hNmod : N % 2 = 1 := by
      have hval := congrArg ZMod.val hN
      have hvalN : (N : ZMod 2).val = N % 2 := ZMod.val_natCast 2 N
      have hval1 : (1 : ZMod 2).val = 1 := by
        change (1 : Fin 2).val = 1
        rfl
      rw [hvalN, hval1] at hval
      exact hval
    have hpowN : gameJ Question ^ N = gameJ Question := by
      have hm := pow_two_eq_one_pow_mod (gameJ_sq (Question := Question)) N
      calc
        gameJ Question ^ N = gameJ Question ^ (N % 2) := hm
        _ = gameJ Question ^ 1 := by rw [hNmod]
        _ = gameJ Question := by simp
    have hpage : ∀ p : Fin 4,
        List.prod (word.map (fun c => gameObservable p (G.reducedQuery c p))) = 1 := by
      intro p
      have hw : (PresentedGroup.mk (InvolutionWord.involutionRels Question)
            ((word.map (fun c => G.reducedQuery c p)).map FreeGroup.of).prod = 1) :=
        (InvolutionWord.wordGroup_mk_prod_eq_one_iff_reducesToEmpty
          (word.map (fun c => G.reducedQuery c p))).mpr (hbal p)
      have hembed := congrArg (pageEmbedding p) hw
      change List.prod (word.map ((fun q : Question => gameObservable p q) ∘
          (fun c : G.ReducedClauseId => G.reducedQuery c p))) = 1
      rw [← List.map_map]
      rw [← pageEmbedding_mk_prod p (word.map (fun c => G.reducedQuery c p))]
      exact hembed
    have hobs : List.prod ((List.finRange 4).map (fun p =>
        (word.map (fun c => gameObservable p (G.reducedQuery c p))).prod)) = 1 := by
      simp [hpage]
    have hprod : (word.map (G.clauseElement hconflict)).prod = gameJ Question := by
      rw [G.clauseElement_word_product_eq, G.clauseObservablePart_word_regroup]
      rw [hobs, one_mul, hpowN]
    exact (mem_clauseSubgroup_iff_exists_list_product G hconflict (gameJ Question)).mpr
      ⟨word, hprod⟩

theorem gameJ_not_mem_clauseSubgroup_iff_noOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    gameJ Question ∉ G.clauseSubgroup hconflict ↔
      ¬ HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  constructor
  · intro hne href
    exact hne ((gameJ_mem_clauseSubgroup_iff_hasOperatorRefutation G hconflict).mpr href)
  · intro hnoref hm
    exact hnoref ((gameJ_mem_clauseSubgroup_iff_hasOperatorRefutation G hconflict).mp hm)

/-- The type of left cosets of the clause subgroup.  This is only a type;
it never carries a quotient-group structure. -/
abbrev ClauseCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : Type uQ :=
  baseGameGroup Question ⧸ G.clauseSubgroup hconflict

/-- Left translation of cosets by a group element. -/
def leftCosetEquiv (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    ClauseCoset G hconflict ≃ ClauseCoset G hconflict where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv x := by
    change g⁻¹ • (g • x) = x
    rw [← mul_smul, inv_mul_cancel, one_smul]
  right_inv x := by
    change g • (g⁻¹ • x) = x
    rw [← mul_smul, mul_inv_cancel, one_smul]

@[simp] theorem leftCosetEquiv_apply (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) (x : ClauseCoset G hconflict) :
    leftCosetEquiv G hconflict g x = g • x := rfl

@[simp] theorem leftCosetEquiv_symm_apply (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) (x : ClauseCoset G hconflict) :
    (leftCosetEquiv G hconflict g).symm x = g⁻¹ • x := rfl

@[simp] theorem leftCosetEquiv_mk (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g x : baseGameGroup Question) :
    leftCosetEquiv G hconflict g (QuotientGroup.mk x) = QuotientGroup.mk (g * x) := by
  rfl

theorem leftCosetEquiv_mul (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g₁ g₂ : baseGameGroup Question) :
    leftCosetEquiv G hconflict (g₁ * g₂) = leftCosetEquiv G hconflict g₁ * leftCosetEquiv G hconflict g₂ := by
  apply Equiv.ext
  intro x
  simp [mul_smul]

theorem leftCosetEquiv_one (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    leftCosetEquiv G hconflict 1 = Equiv.refl _ := by
  apply Equiv.ext
  intro x
  simp

/-- The forward reindexing map on `ℓ²`. -/
def lpReindexToFun {α : Type uL} {β : Type uL} (e : α ≃ β)
    (f : lp (fun _ : α => ℂ) 2) : lp (fun _ : β => ℂ) 2 :=
  ⟨fun b => f (e.symm b), by
    change Memℓp (fun b : β => (f : ∀ a : α, ℂ) (e.symm b)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact (Equiv.summable_iff e.symm).2
      ((memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp f))⟩

/-- The inverse reindexing map on `ℓ²`. -/
def lpReindexInvFun {α : Type uL} {β : Type uL} (e : α ≃ β)
    (g : lp (fun _ : β => ℂ) 2) : lp (fun _ : α => ℂ) 2 :=
  ⟨fun a => g (e a), by
    change Memℓp (fun a : α => (g : ∀ b : β, ℂ) (e a)) 2
    rw [memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
    exact (Equiv.summable_iff e).2
      ((memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).1 (lp.memℓp g))⟩

/-- Reindex an `ℓ²` space along an index equivalence. -/
def lpReindex {α : Type uL} {β : Type uL} (e : α ≃ β) :
    lp (fun _ : α => ℂ) 2 ≃ₗᵢ[ℂ] lp (fun _ : β => ℂ) 2 where
  toFun := lpReindexToFun e
  invFun := lpReindexInvFun e
  map_add' f g := by
    apply Subtype.ext
    funext b
    rfl
  map_smul' c f := by
    apply Subtype.ext
    funext b
    rfl
  norm_map' f := by
    have hto : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    have h1 : ‖lpReindexToFun e f‖ ^ 2 = ∑' b, ‖(f : ∀ a : α, ℂ) (e.symm b)‖ ^ 2 := by
      change ‖lpReindexToFun e f‖ ^ 2 = ∑' b : β, ‖(f : ∀ a : α, ℂ) (e.symm b)‖ ^ 2
      simpa [hto, lpReindexToFun] using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (lpReindexToFun e f))
    have h2 : ‖f‖ ^ 2 = ∑' a, ‖(f : ∀ a : α, ℂ) a‖ ^ 2 := by
      change ‖f‖ ^ 2 = ∑' a : α, ‖(f : ∀ a : α, ℂ) a‖ ^ 2
      simpa [hto] using
        (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) f)
    have htsum : (∑' b : β, ‖(f : ∀ a : α, ℂ) (e.symm b)‖ ^ 2) =
        ∑' a : α, ‖(f : ∀ a : α, ℂ) a‖ ^ 2 := by
      exact Equiv.tsum_eq e.symm (fun a : α => ‖(f : ∀ a : α, ℂ) a‖ ^ 2)
    have hsq : ‖lpReindexToFun e f‖ ^ 2 = ‖f‖ ^ 2 := by
      rw [h1, htsum, h2]
    have hnonneg1 : 0 ≤ ‖lpReindexToFun e f‖ := norm_nonneg _
    have hnonneg2 : 0 ≤ ‖f‖ := norm_nonneg _
    change ‖lpReindexToFun e f‖ = ‖f‖
    nlinarith
  left_inv g := by
    apply Subtype.ext
    funext a
    change (lpReindexToFun e g).1 (e a) = g.1 a
    change g.1 (e.symm (e a)) = g.1 a
    rw [e.symm_apply_apply]
  right_inv f := by
    apply Subtype.ext
    funext b
    change (lpReindexToFun e (lpReindexInvFun e f)).1 b = f.1 b
    change (lpReindexInvFun e f).1 (e.symm b) = f.1 b
    change f.1 (e (e.symm b)) = f.1 b
    rw [e.apply_symm_apply]

@[simp] theorem lpReindex_single {α : Type uL} {β : Type uL} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (a : α) :
    lpReindex e (lp.single 2 a (1 : ℂ)) = lp.single 2 (e a) (1 : ℂ) := by
  classical
  apply Subtype.ext
  funext b
  by_cases h : b = e a
  · subst b
    simp [lpReindex, lpReindexToFun, lp.single, Pi.single]
    rw [e.symm_apply_apply]
    simp
  · have hne : e.symm b ≠ a := by
      intro hh
      apply h
      calc
        b = e (e.symm b) := (e.apply_symm_apply b).symm
        _ = e a := by rw [hh]
    simp [lpReindex, lpReindexToFun, lp.single, Pi.single, h, hne]

/-- The genuine `ℓ²` space over the left cosets. -/
abbrev CosetHilbert (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : Type uQ :=
  lp (fun _ : ClauseCoset G hconflict => ℂ) 2

/-- Left translation on `ℓ²` of the cosets. -/
def leftTranslation (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    CosetHilbert G hconflict →L[ℂ] CosetHilbert G hconflict :=
  (lpReindex (leftCosetEquiv G hconflict g)).toLinearIsometry.toContinuousLinearMap

theorem leftTranslation_single (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question)
    (x : ClauseCoset G hconflict) [DecidableEq (ClauseCoset G hconflict)] :
    leftTranslation G hconflict g (lp.single 2 x (1 : ℂ)) =
      lp.single 2 (g • x) (1 : ℂ) := by
  simp [leftTranslation, lpReindex_single]

theorem leftTranslation_one (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    leftTranslation G hconflict 1 = 1 := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change f ((leftCosetEquiv G hconflict 1).symm x) = f x
  have hs : (leftCosetEquiv G hconflict 1).symm x = x := by
    change (1 : baseGameGroup Question)⁻¹ • x = x
    simp
  rw [hs]

theorem leftTranslation_mul (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g₁ g₂ : baseGameGroup Question) :
    leftTranslation G hconflict (g₁ * g₂) =
      leftTranslation G hconflict g₁ * leftTranslation G hconflict g₂ := by
  apply ContinuousLinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change ((lpReindex (leftCosetEquiv G hconflict (g₁ * g₂))) f).1 x =
    ((lpReindex (leftCosetEquiv G hconflict g₁))
      ((lpReindex (leftCosetEquiv G hconflict g₂)) f)).1 x
  simp [lpReindex, lpReindexToFun, mul_inv_rev, mul_smul]

theorem leftTranslation_commute (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) {g₁ g₂ : baseGameGroup Question}
    (hc : Commute g₁ g₂) :
    Commute (leftTranslation G hconflict g₁) (leftTranslation G hconflict g₂) := by
  unfold Commute SemiconjBy
  rw [← leftTranslation_mul, ← leftTranslation_mul]
  congr 1

theorem leftCosetEquiv_symm (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    (leftCosetEquiv G hconflict g).symm = leftCosetEquiv G hconflict g⁻¹ := by
  apply Equiv.ext
  intro x
  rfl

theorem lpReindex_symm {α : Type uL} {β : Type uL} (e : α ≃ β) :
    (lpReindex e).symm = lpReindex e.symm := by
  apply LinearIsometryEquiv.ext
  intro f
  apply Subtype.ext
  funext a
  change f (e a) = f (e.symm.symm a)
  rw [Equiv.symm_symm]

theorem leftTranslation_adjoint (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    ContinuousLinearMap.adjoint (leftTranslation G hconflict g) =
      leftTranslation G hconflict g⁻¹ := by
  unfold leftTranslation
  rw [show ContinuousLinearMap.adjoint
      ((lpReindex (leftCosetEquiv G hconflict g)).toLinearIsometry.toContinuousLinearMap) =
      (lpReindex (leftCosetEquiv G hconflict g)).symm.toLinearIsometry.toContinuousLinearMap by
    exact LinearIsometryEquiv.adjoint_eq_symm (lpReindex (leftCosetEquiv G hconflict g))]
  rw [lpReindex_symm, leftCosetEquiv_symm]

/-- Left translation by a group element and its inverse are mutual
inverses. -/
theorem leftTranslation_inv (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    leftTranslation G hconflict g⁻¹ * leftTranslation G hconflict g = 1 ∧
      leftTranslation G hconflict g * leftTranslation G hconflict g⁻¹ = 1 := by
  constructor
  · rw [← leftTranslation_mul]
    rw [inv_mul_cancel]
    exact leftTranslation_one G hconflict
  · rw [← leftTranslation_mul]
    rw [mul_inv_cancel]
    exact leftTranslation_one G hconflict

/-- Left translation by a group element is a unitary operator on the coset
space. -/
theorem leftTranslation_isUnitary (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (g : baseGameGroup Question) :
    leftTranslation G hconflict g ∈
      unitary (CosetHilbert G hconflict →L[ℂ] CosetHilbert G hconflict) := by
  rw [Unitary.mem_iff]
  have hstar : star (leftTranslation G hconflict g) = leftTranslation G hconflict g⁻¹ := by
    change ContinuousLinearMap.adjoint (leftTranslation G hconflict g) =
      leftTranslation G hconflict g⁻¹
    exact leftTranslation_adjoint G hconflict g
  constructor
  · rw [hstar]
    rw [← leftTranslation_mul]
    rw [inv_mul_cancel]
    exact leftTranslation_one G hconflict
  · rw [hstar]
    rw [← leftTranslation_mul]
    rw [mul_inv_cancel]
    exact leftTranslation_one G hconflict

/-- The identity coset. -/
def baseCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : ClauseCoset G hconflict :=
  QuotientGroup.mk (1 : baseGameGroup Question)

/-- The coset of `J`. -/
def jCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : ClauseCoset G hconflict :=
  gameJ Question • baseCoset G hconflict

theorem baseCoset_ne_jCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) :
    baseCoset G hconflict ≠ jCoset G hconflict := by
  intro h
  have hmk : (QuotientGroup.mk (1 : baseGameGroup Question) : ClauseCoset G hconflict) =
      QuotientGroup.mk (gameJ Question) := by
    simpa [baseCoset, jCoset, mul_one] using h
  have hmem : (1 : baseGameGroup Question)⁻¹ * gameJ Question ∈ G.clauseSubgroup hconflict := by
    exact (QuotientGroup.eq (s := G.clauseSubgroup hconflict)).mp hmk
  have hg : (1 : baseGameGroup Question)⁻¹ * gameJ Question = gameJ Question := by simp
  exact hJ (by simpa [hg] using hmem)

/-- The singleton vector at the identity coset. -/
def baseState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    CosetHilbert G hconflict :=
  lp.single (E := fun _ : ClauseCoset G hconflict => ℂ) 2 (baseCoset G hconflict) (1 : ℂ)

/-- The singleton vector at the `J` coset. -/
def jState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    CosetHilbert G hconflict :=
  lp.single (E := fun _ : ClauseCoset G hconflict => ℂ) 2 (jCoset G hconflict) (1 : ℂ)

/-- The normalized difference of the two distinguished coset vectors. -/
def cosetState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    CosetHilbert G hconflict :=
  (1 / Real.sqrt 2 : ℂ) • (baseState G hconflict - jState G hconflict)

set_option maxHeartbeats 400000 in
private theorem cosetState_norm_aux (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) :
    ‖baseState G hconflict - jState G hconflict‖ = Real.sqrt 2 := by
  classical
  let a : CosetHilbert G hconflict := baseState G hconflict
  let b : CosetHilbert G hconflict := jState G hconflict
  have hne : baseCoset G hconflict ≠ jCoset G hconflict := baseCoset_ne_jCoset G hconflict hJ
  have hab : inner ℂ a b = 0 := by
    change inner ℂ (baseState G hconflict) (jState G hconflict) = 0
    rw [baseState, jState]
    rw [lp.inner_single_left (i := baseCoset G hconflict) (a := (1 : ℂ))
      (f := (lp.single (E := fun _ : ClauseCoset G hconflict => ℂ) 2
        (jCoset G hconflict) (1 : ℂ) : CosetHilbert G hconflict))]
    have hb0 : (lp.single (E := fun _ : ClauseCoset G hconflict => ℂ) 2
        (jCoset G hconflict) (1 : ℂ) : ∀ x : ClauseCoset G hconflict, ℂ)
        (baseCoset G hconflict) = 0 := by
      exact lp.single_apply_ne (E := fun _ : ClauseCoset G hconflict => ℂ) 2
        (jCoset G hconflict) (1 : ℂ) hne
    rw [hb0]
    simp
  have hab2 : ‖a - b‖ ^ 2 = 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    have ha : ‖a‖ ^ 2 = 1 := by simp [a, baseState, lp.norm_single]
    have hb : ‖b‖ ^ 2 = 1 := by simp [b, jState, lp.norm_single]
    rw [hab, ha, hb]
    norm_num
  have hnonneg : 0 ≤ ‖a - b‖ := norm_nonneg _
  rw [← hab2, Real.sqrt_sq_eq_abs, abs_of_nonneg hnonneg]

set_option maxHeartbeats 400000 in
theorem cosetState_norm (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) :
    ‖cosetState G hconflict‖ = 1 := by
  classical
  rw [cosetState]
  rw [norm_smul]
  have hsqrt : ‖baseState G hconflict - jState G hconflict‖ = Real.sqrt 2 :=
    cosetState_norm_aux G hconflict hJ
  rw [hsqrt]
  have hsqrtpos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hc : ‖(1 / Real.sqrt 2 : ℂ)‖ = 1 / Real.sqrt 2 := by
    rw [norm_div]
    rw [Complex.norm_real]
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (le_of_lt hsqrtpos)]
    rw [norm_one]
  rw [hc]
  rw [div_mul_cancel₀ _ hsqrtpos.ne']

theorem leftTranslation_gameJ_single_base (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    leftTranslation G hconflict (gameJ Question) (baseState G hconflict) =
      jState G hconflict := by
  classical
  rw [baseState, jState]
  rw [leftTranslation_single]
  rfl

theorem leftTranslation_gameJ_single_j (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    leftTranslation G hconflict (gameJ Question) (jState G hconflict) =
      baseState G hconflict := by
  classical
  rw [jState, baseState]
  rw [leftTranslation_single]
  -- gameJ • jCoset = baseCoset
  congr 1
  change gameJ Question • (gameJ Question • baseCoset G hconflict) = baseCoset G hconflict
  rw [← mul_smul]
  -- gameJ * gameJ = 1
  rw [gameJ_sq]
  simp

theorem leftTranslation_gameJ_cosetState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)] :
    leftTranslation G hconflict (gameJ Question) (cosetState G hconflict) =
      - cosetState G hconflict := by
  classical
  rw [cosetState]
  -- linearity
  rw [map_smul, map_sub]
  rw [leftTranslation_gameJ_single_base, leftTranslation_gameJ_single_j]
  rw [smul_sub, smul_sub, neg_sub]

theorem clauseSubgroup_smul_baseCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) {h : baseGameGroup Question}
    (hh : h ∈ G.clauseSubgroup hconflict) :
    h • baseCoset G hconflict = baseCoset G hconflict := by
  change h • (QuotientGroup.mk (1 : baseGameGroup Question) : ClauseCoset G hconflict) =
    QuotientGroup.mk (1 : baseGameGroup Question)
  -- h • mk 1 = mk (h * 1) = mk h
  have hmk : h • (QuotientGroup.mk (1 : baseGameGroup Question) : ClauseCoset G hconflict) =
      QuotientGroup.mk (h * 1) := rfl
  rw [hmk]
  -- mk (h*1) = mk 1 since 1⁻¹ * h = h ∈ H
  have hm : (QuotientGroup.mk (h * 1) : ClauseCoset G hconflict) = QuotientGroup.mk (1 : baseGameGroup Question) := by
    exact (QuotientGroup.eq (s := G.clauseSubgroup hconflict)).mpr (by simpa using hh)
  rw [hm]

private theorem inv_eq_self_of_sq_eq_one {M : Type uM} [Group M] {a : M}
    (h : a * a = 1) : a⁻¹ = a := by
  calc
    a⁻¹ = a⁻¹ * 1 := by rw [mul_one]
    _ = a⁻¹ * (a * a) := by rw [h]
    _ = (a⁻¹ * a) * a := by rw [← mul_assoc]
    _ = 1 * a := by rw [inv_mul_cancel]
    _ = a := by rw [one_mul]

theorem clauseSubgroup_smul_jCoset (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) {h : baseGameGroup Question}
    (hh : h ∈ G.clauseSubgroup hconflict) :
    h • jCoset G hconflict = jCoset G hconflict := by
  change h • (gameJ Question • baseCoset G hconflict) = gameJ Question • baseCoset G hconflict
  rw [← mul_smul]
  -- h * gameJ • baseCoset = gameJ • baseCoset: need mk ((h*gameJ)*1) = mk (gameJ*1)
  change (QuotientGroup.mk ((h * gameJ Question) * 1) : ClauseCoset G hconflict) =
    QuotientGroup.mk (gameJ Question * 1)
  -- (h*gameJ)⁻¹ * gameJ ∈ H: = gameJ * h⁻¹ * gameJ = h⁻¹ (J central)
  have hm : (QuotientGroup.mk ((h * gameJ Question) * 1) : ClauseCoset G hconflict) =
      QuotientGroup.mk (gameJ Question * 1) := by
    apply (QuotientGroup.eq (s := G.clauseSubgroup hconflict)).mpr
    -- ((h * J) * 1)⁻¹ * (J * 1) = (h*J)⁻¹ * J ∈ H
    have hmem : (h * gameJ Question)⁻¹ * gameJ Question ∈ G.clauseSubgroup hconflict := by
      -- (h*J)⁻¹ * J = J * h⁻¹ * J = h⁻¹ (J central)
      have hcalc : (h * gameJ Question)⁻¹ * gameJ Question = h⁻¹ := by
        calc
          (h * gameJ Question)⁻¹ * gameJ Question
              = (gameJ Question)⁻¹ * h⁻¹ * gameJ Question := by rw [mul_inv_rev]
          _ = gameJ Question * h⁻¹ * gameJ Question := by
                rw [inv_eq_self_of_sq_eq_one (gameJ_sq (Question := Question))]
          _ = h⁻¹ := by
                have hc : Commute (gameJ Question) h⁻¹ := gameJ_central h⁻¹
                calc
                  (gameJ Question * h⁻¹) * gameJ Question
                      = (h⁻¹ * gameJ Question) * gameJ Question := by rw [hc.eq]
                  _ = h⁻¹ := by rw [mul_assoc, gameJ_sq, mul_one]
      rw [hcalc]
      exact (G.clauseSubgroup hconflict).inv_mem hh
    simpa using hmem
  rw [hm]

theorem leftTranslation_clauseElement_single_base (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (c : G.ReducedClauseId) :
    leftTranslation G hconflict (G.clauseElement hconflict c) (baseState G hconflict) =
      baseState G hconflict := by
  classical
  rw [baseState]
  rw [leftTranslation_single]
  congr 1
  exact clauseSubgroup_smul_baseCoset G hconflict (Subgroup.subset_closure ⟨c, rfl⟩)

theorem leftTranslation_clauseElement_single_j (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (c : G.ReducedClauseId) :
    leftTranslation G hconflict (G.clauseElement hconflict c) (jState G hconflict) =
      jState G hconflict := by
  classical
  rw [jState]
  rw [leftTranslation_single]
  congr 1
  exact clauseSubgroup_smul_jCoset G hconflict (Subgroup.subset_closure ⟨c, rfl⟩)

theorem leftTranslation_clauseElement_cosetState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (c : G.ReducedClauseId) :
    leftTranslation G hconflict (G.clauseElement hconflict c) (cosetState G hconflict) =
      cosetState G hconflict := by
  classical
  rw [cosetState]
  rw [map_smul, map_sub]
  rw [leftTranslation_clauseElement_single_base, leftTranslation_clauseElement_single_j]

/-- Left translation by a power of `J` acts on the coset state by the binary
XOR phase. -/
theorem leftTranslation_gameJ_pow_cosetState (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (s : ZMod 2) :
    leftTranslation G hconflict (gameJ Question ^ s.val) (cosetState G hconflict) =
      binaryXORPhase s • cosetState G hconflict := by
  rcases zmodTwo_eq_zero_or_one s with hs | hs
  · subst s
    have hval : (0 : ZMod 2).val = 0 := by norm_num
    rw [hval]
    rw [pow_zero, leftTranslation_one]
    simp [binaryXORPhase_zero]
  · subst s
    have hval : (1 : ZMod 2).val = 1 := by decide
    rw [hval]
    rw [pow_one, leftTranslation_gameJ_cosetState]
    simp [binaryXORPhase_one]

/-- The observable part of a clause acts on the coset state by the signed
clause phase. -/
theorem leftTranslation_clauseObservablePart_cosetState
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (c : G.ReducedClauseId) :
    leftTranslation G hconflict (G.clauseObservablePart c) (cosetState G hconflict) =
      binaryXORPhase (G.reducedSign hconflict c) • cosetState G hconflict := by
  classical
  let s : ZMod 2 := G.reducedSign hconflict c
  let A : CosetHilbert G hconflict →L[ℂ] CosetHilbert G hconflict :=
    leftTranslation G hconflict (G.clauseObservablePart c)
  let ψ : CosetHilbert G hconflict := cosetState G hconflict
  have hphase2 : binaryXORPhase s * binaryXORPhase s = 1 := by
    rw [← binaryXORPhase_add]
    have htwo : s + s = 0 := by
      rcases zmodTwo_eq_zero_or_one s with hs | hs
      · simp [hs]
      · rw [hs]
        decide
    rw [htwo]
    simp [binaryXORPhase_zero]
  have hfix : leftTranslation G hconflict (G.clauseElement hconflict c) ψ = ψ := by
    exact leftTranslation_clauseElement_cosetState G hconflict c
  have hmul : leftTranslation G hconflict (G.clauseElement hconflict c) =
      A * leftTranslation G hconflict (gameJ Question ^ s.val) := by
    simpa [A] using
      leftTranslation_mul G hconflict (G.clauseObservablePart c) (gameJ Question ^ s.val)
  have hpow : leftTranslation G hconflict (gameJ Question ^ s.val) ψ =
      binaryXORPhase s • ψ := by
    simpa [ψ, s] using leftTranslation_gameJ_pow_cosetState G hconflict s
  have heq : A (binaryXORPhase s • ψ) = ψ := by
    have h1 : A (leftTranslation G hconflict (gameJ Question ^ s.val) ψ) = ψ := by
      calc
        A (leftTranslation G hconflict (gameJ Question ^ s.val) ψ)
            = (A * leftTranslation G hconflict (gameJ Question ^ s.val)) ψ := by
                rfl
        _ = leftTranslation G hconflict (G.clauseElement hconflict c) ψ := by
                rw [← hmul]
        _ = ψ := hfix
    rw [hpow] at h1
    exact h1
  have heq' : binaryXORPhase s • A ψ = ψ := by
    rw [map_smul] at heq
    exact heq
  calc
    A ψ = (1 : ℂ) • A ψ := by simp
    _ = (binaryXORPhase s * binaryXORPhase s) • A ψ := by rw [hphase2]
    _ = binaryXORPhase s • (binaryXORPhase s • A ψ) := by rw [smul_smul]
    _ = binaryXORPhase s • ψ := by rw [heq']

/-- The explicit left-coset commuting-operator strategy. -/
def cosetStrategy (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) :
    FourPlayerCommutingOperatorStrategy Question (CosetHilbert G hconflict) where
  state := cosetState G hconflict
  state_norm := cosetState_norm G hconflict hJ
  observable p q := leftTranslation G hconflict (gameObservable p q)
  isSelfAdjoint := by
    intro p q
    unfold IsSelfAdjoint
    change ContinuousLinearMap.adjoint (leftTranslation G hconflict (gameObservable p q)) =
      leftTranslation G hconflict (gameObservable p q)
    rw [leftTranslation_adjoint]
    congr 1
    exact inv_eq_self_of_sq_eq_one (gameObservable_sq p q)
  involutive := by
    intro p q
    rw [← leftTranslation_mul]
    rw [gameObservable_sq]
    exact leftTranslation_one G hconflict
  cross_commute := by
    intro p p' hne q q'
    exact leftTranslation_commute G hconflict (gameObservable_cross_commute hne q q')

/-- In the coset strategy the ordered clause operator is the left translation
by the clause observable part. -/
theorem cosetStrategy_clauseOperator_eq_leftTranslation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) (c : G.ReducedClauseId) :
    FourPlayerCommutingOperatorStrategy.clauseOperator (cosetStrategy G hconflict hJ)
        (G.reducedQuery c) =
      leftTranslation G hconflict (G.clauseObservablePart c) := by
  calc
    FourPlayerCommutingOperatorStrategy.clauseOperator (cosetStrategy G hconflict hJ)
        (G.reducedQuery c)
        = leftTranslation G hconflict (gameObservable 0 (G.reducedQuery c 0)) *
          leftTranslation G hconflict (gameObservable 1 (G.reducedQuery c 1)) *
          leftTranslation G hconflict (gameObservable 2 (G.reducedQuery c 2)) *
          leftTranslation G hconflict (gameObservable 3 (G.reducedQuery c 3)) := by
          simp [FourPlayerCommutingOperatorStrategy.clauseOperator, cosetStrategy]
    _ = leftTranslation G hconflict
          (gameObservable 0 (G.reducedQuery c 0) *
            gameObservable 1 (G.reducedQuery c 1) *
            gameObservable 2 (G.reducedQuery c 2) *
            gameObservable 3 (G.reducedQuery c 3)) := by
          rw [← leftTranslation_mul, ← leftTranslation_mul, ← leftTranslation_mul]
    _ = leftTranslation G hconflict (G.clauseObservablePart c) := by
          congr 1

/-- Every reduced signed clause is satisfied by the coset strategy. -/
theorem cosetStrategy_satisfiesSignedClause
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) (c : G.ReducedClauseId) :
    (cosetStrategy G hconflict hJ).SatisfiesSignedClause (G.reducedQuery c)
      (G.reducedSign hconflict c) := by
  unfold FourPlayerCommutingOperatorStrategy.SatisfiesSignedClause
  simpa [cosetStrategy, FourPlayerCommutingOperatorStrategy.clauseOperator,
    clauseObservablePart, ← leftTranslation_mul, mul_assoc, mul_one] using
    leftTranslation_clauseObservablePart_cosetState G hconflict c

/-- The bundled coset model witnessing a perfect commuting-operator strategy. -/
def cosetModel (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) [DecidableEq (ClauseCoset G hconflict)]
    (hJ : gameJ Question ∉ G.clauseSubgroup hconflict) :
    FourPlayerCommutingOperatorStrategy.PerfectCommutingOperatorModel G where
  Hilbert := CosetHilbert G hconflict
  strategy := cosetStrategy G hconflict hJ
  perfect := by
    intro clause hclause
    classical
    rw [raw_support_eq_reduced_support G hconflict] at hclause
    rcases Finset.mem_image.mp hclause with ⟨c, hc, rfl⟩
    simpa [reducedSignedClause, reducedQuery] using
      cosetStrategy_satisfiesSignedClause G hconflict hJ c

/-- Absence of an operator refutation gives a perfect commuting-operator
strategy on the coset space. -/
theorem noOperatorRefutation_implies_hasPerfectCommutingOperatorStrategy
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hnoref : ¬ HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict)) :
    FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G := by
  classical
  letI := Classical.decEq (ClauseCoset G hconflict)
  have hJ : gameJ Question ∉ G.clauseSubgroup hconflict :=
    (gameJ_not_mem_clauseSubgroup_iff_noOperatorRefutation G hconflict).mpr hnoref
  exact ⟨cosetModel G hconflict hJ⟩

/-- A game has a perfect commuting-operator strategy exactly when it has no
operator refutation. -/
theorem hasPerfectCommutingOperatorStrategy_iff_noOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G ↔
      ¬ HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  constructor
  · intro hmodel href
    rcases hmodel with ⟨model⟩
    letI := model.normedAddCommGroup
    letI := model.innerProductSpace
    letI := model.completeSpace
    have hperf : FourPlayerCommutingOperatorStrategy.IsPerfectCommutingOperatorStrategy
        G.reducedQuery (G.reducedSign hconflict) model.strategy := by
      intro c
      simpa [reducedSignedClause, reducedQuery] using
        model.perfect (G.reducedSignedClause hconflict c)
          (G.reducedSignedClause_mem_support hconflict c)
    exact (FourPlayerCommutingOperatorStrategy.operatorRefutation_excludes_perfectCommutingOperatorStrategy
      G.reducedQuery (G.reducedSign hconflict) model.strategy href) hperf
  · intro hnoref
    exact noOperatorRefutation_implies_hasPerfectCommutingOperatorStrategy G hconflict hnoref

end FiniteFourPlayerXORGame

end

end XORGame
end QIT

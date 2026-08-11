/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic

/-!
# Canonical finite weighted XOR-game data

This module introduces the canonical data shape for a finite, weighted,
four-player binary XOR game.  A game is a weight function on signed question
tuples, so repeated indexed clauses with the same tuple and sign are already
aggregated.  Clauses with zero weight impose no constraint.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uC

noncomputable section

/-- An unsigned four-player question tuple. -/
abbrev FourPlayerQuestionTuple (Question : Type uQ) :=
  Fin 4 → Question

/-- A signed four-player clause: an unsigned question tuple together with the
binary XOR target sign. -/
abbrev SignedFourPlayerClause (Question : Type uQ) :=
  FourPlayerQuestionTuple Question × ZMod 2

/--
A finite weighted four-player binary XOR game.

The weight function lives on *signed* question tuples, so duplicate indexed
clauses with the same tuple and sign are represented by adding their weights.
Zero-weight clauses impose no perfectness condition.
-/
structure FiniteFourPlayerXORGame
    (Question : Type uQ) [Fintype Question] [DecidableEq Question] where
  /-- The nonnegative weight of each signed clause. -/
  weight : SignedFourPlayerClause Question → ℝ
  /-- Weights are nonnegative. -/
  weight_nonneg : ∀ clause, 0 ≤ weight clause
  /-- The total weight is normalized to one. -/
  weight_sum_one : ∑ clause, weight clause = 1

namespace FiniteFourPlayerXORGame

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

/-- The strict-positive-weight support of a game. -/
def support (G : FiniteFourPlayerXORGame Question) :
    Finset (SignedFourPlayerClause Question) := by
  classical
  exact Finset.univ.filter fun clause => 0 < G.weight clause

@[simp]
theorem mem_support_iff (G : FiniteFourPlayerXORGame Question)
    (clause : SignedFourPlayerClause Question) :
    clause ∈ G.support ↔ 0 < G.weight clause := by
  simp [support]

/-- The support is nonempty because the total weight is one. -/
theorem support_nonempty (G : FiniteFourPlayerXORGame Question) :
    G.support.Nonempty := by
  classical
  by_contra hne
  have hsum : (∑ clause : SignedFourPlayerClause Question, G.weight clause) = 0 := by
    apply Finset.sum_eq_zero
    intro clause hclause
    have hnot : ¬ 0 < G.weight clause := by
      intro hpos
      exact hne ⟨clause, (G.mem_support_iff clause).mpr hpos⟩
    exact le_antisymm (not_lt.mp hnot) (G.weight_nonneg clause)
  rw [G.weight_sum_one] at hsum
  norm_num at hsum

/-- The questions that occur with positive weight for a player. -/
def activeQuestions (G : FiniteFourPlayerXORGame Question) (p : Fin 4) :
    Finset Question := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ clause : SignedFourPlayerClause Question,
      0 < G.weight clause ∧ clause.1 p = q

@[simp]
theorem mem_activeQuestions_iff (G : FiniteFourPlayerXORGame Question)
    (p : Fin 4) (q : Question) :
    q ∈ G.activeQuestions p ↔
      ∃ clause : SignedFourPlayerClause Question,
        0 < G.weight clause ∧ clause.1 p = q := by
  simp [activeQuestions]

/-- The maximum, over the four players, of the number of active questions. -/
def activeQuestionBound (G : FiniteFourPlayerXORGame Question) : ℕ :=
  (Finset.univ : Finset (Fin 4)).sup fun p : Fin 4 =>
    (G.activeQuestions p).card

/-- Each player's active-question count is bounded by the game bound. -/
theorem activeQuestions_card_le_activeQuestionBound
    (G : FiniteFourPlayerXORGame Question) (p : Fin 4) :
    (G.activeQuestions p).card ≤ G.activeQuestionBound := by
  unfold activeQuestionBound
  exact Finset.le_sup (α := ℕ) (β := Fin 4)
    (s := (Finset.univ : Finset (Fin 4)))
    (f := fun p : Fin 4 => (G.activeQuestions p).card)
    (b := p)
    (show p ∈ (Finset.univ : Finset (Fin 4)) from Finset.mem_univ p)

/-- The active-question bound is at most `n` exactly when every player has at
most `n` active questions. -/
theorem activeQuestionBound_le_iff (G : FiniteFourPlayerXORGame Question)
    (n : ℕ) :
    G.activeQuestionBound ≤ n ↔
      ∀ p : Fin 4, (G.activeQuestions p).card ≤ n := by
  unfold activeQuestionBound
  rw [Finset.sup_le_iff]
  simp

/-- A target conflict is an unsigned query occurring at positive weight with
both possible target signs. -/
def HasConflictingTargets (G : FiniteFourPlayerXORGame Question) : Prop :=
  ∃ query : FourPlayerQuestionTuple Question,
    0 < G.weight (query, (0 : ZMod 2)) ∧
      0 < G.weight (query, (1 : ZMod 2))

/--
The indexed constructor aggregates indexed clause weights by their signed
question tuple.
-/
def ofIndexed
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1) :
    FiniteFourPlayerXORGame Question where
  weight clause :=
    ∑ c : ClauseId,
      if query c = clause.1 ∧ sign c = clause.2 then weight c else 0
  weight_nonneg := by
    intro clause
    exact Finset.sum_nonneg (by
      intro c hc
      by_cases h : query c = clause.1 ∧ sign c = clause.2
      · simp [h, hweight_nonneg c]
      · simp [h])
  weight_sum_one := by
    classical
    rw [← hweight_sum_one]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro c hc
    have hsum :
        (∑ b : SignedFourPlayerClause Question,
            if query c = b.1 ∧ sign c = b.2 then weight c else 0) =
          weight c := by
      simpa using (Finset.sum_eq_single
        (s := (Finset.univ : Finset (SignedFourPlayerClause Question)))
        (a := (query c, sign c))
        (f := fun b : SignedFourPlayerClause Question =>
          if query c = b.1 ∧ sign c = b.2 then weight c else 0)
        (by intro b hb hne
            have hnot : ¬ (query c = b.1 ∧ sign c = b.2) := by
              intro h
              exact hne (Prod.ext h.1.symm h.2.symm)
            simp [hnot])
        (by intro hnotmem
            exact False.elim (hnotmem (Finset.mem_univ _))))
    exact hsum

@[simp]
theorem ofIndexed_weight
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (clause : SignedFourPlayerClause Question) :
    (ofIndexed query sign weight hweight_nonneg hweight_sum_one).weight clause =
      ∑ c : ClauseId,
        if query c = clause.1 ∧ sign c = clause.2 then weight c else 0 :=
  rfl

/-- Duplicate indexed clauses with the same question tuple and sign merge to
the same aggregated weight. -/
theorem ofIndexed_merges_duplicates
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (c₁ c₂ : ClauseId) (hq : query c₁ = query c₂) (hs : sign c₁ = sign c₂) :
    (ofIndexed query sign weight hweight_nonneg hweight_sum_one).weight
        (query c₁, sign c₁) =
      (ofIndexed query sign weight hweight_nonneg hweight_sum_one).weight
        (query c₂, sign c₂) := by
  rw [hq, hs]

/-- If the only indexed representative of a signed tuple has zero weight,
that signed tuple is not in the aggregated support. -/
theorem ofIndexed_zero_weight_not_mem_support
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (c : ClauseId) (hzero : weight c = 0)
    (honly : ∀ d : ClauseId, query d = query c ∧ sign d = sign c → d = c) :
    (query c, sign c) ∉
      (ofIndexed query sign weight hweight_nonneg hweight_sum_one).support := by
  classical
  rw [mem_support_iff]
  rw [ofIndexed_weight]
  intro hpos
  have hsum : (∑ d : ClauseId,
      if query d = query c ∧ sign d = sign c then weight d else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    by_cases h : query d = query c ∧ sign d = sign c
    · have : d = c := honly d h
      subst d
      simp [hzero]
    · simp [h]
  rw [hsum] at hpos
  norm_num at hpos

end FiniteFourPlayerXORGame

/-! ## Small worked examples -/

namespace FiniteGameExamples

open scoped BigOperators

abbrev Q3 := Fin 3
abbrev C4 := Fin 4

/-- A query map with indices `0` and `1` sharing one tuple, index `2` on
another tuple, and index `3` on a third tuple. -/
def exQuery : C4 → FourPlayerQuestionTuple Q3 :=
  fun c _ =>
    if c = 0 then (0 : Q3)
    else if c = 1 then (0 : Q3)
    else if c = 2 then (1 : Q3)
    else (2 : Q3)

theorem exQuery_zero : exQuery 0 = (fun _ : Fin 4 => (0 : Q3)) := by
  funext p
  simp [exQuery]

theorem exQuery_one : exQuery 1 = (fun _ : Fin 4 => (0 : Q3)) := by
  funext p
  simp [exQuery]

theorem exQuery_two : exQuery 2 = (fun _ : Fin 4 => (1 : Q3)) := by
  funext p
  simp [exQuery]

theorem exQuery_three : exQuery 3 = (fun _ : Fin 4 => (2 : Q3)) := by
  funext p
  simp [exQuery]

/-- Signs: indices `0`, `1`, `2` have target `0`; index `3` has target `1`. -/
def exSign : C4 → ZMod 2 :=
  fun c =>
    if c = 3 then (1 : ZMod 2) else (0 : ZMod 2)

theorem exSign_zero : exSign 0 = (0 : ZMod 2) := by
  simp [exSign]

theorem exSign_one : exSign 1 = (0 : ZMod 2) := by
  simp [exSign]

theorem exSign_two : exSign 2 = (0 : ZMod 2) := by
  simp [exSign]

theorem exSign_three : exSign 3 = (1 : ZMod 2) := by
  simp [exSign]

/-- Weights: `1/3` on indices `0`, `1`, `2` and zero on index `3`. -/
def exWeight : C4 → ℝ :=
  fun c =>
    if c = 0 then (1 / 3 : ℝ)
    else if c = 1 then (1 / 3 : ℝ)
    else if c = 2 then (1 / 3 : ℝ)
    else 0

theorem exWeight_zero : exWeight 0 = (1 / 3 : ℝ) := by
  simp [exWeight]

theorem exWeight_one : exWeight 1 = (1 / 3 : ℝ) := by
  simp [exWeight]

theorem exWeight_two : exWeight 2 = (1 / 3 : ℝ) := by
  simp [exWeight]

theorem exWeight_three : exWeight 3 = 0 := by
  simp [exWeight]

theorem const_zero_ne_const_one :
    (fun _ : Fin 4 => (0 : Q3)) ≠ (fun _ : Fin 4 => (1 : Q3)) := by
  decide

theorem const_one_ne_const_zero :
    (fun _ : Fin 4 => (1 : Q3)) ≠ (fun _ : Fin 4 => (0 : Q3)) := by
  decide

theorem const_zero_ne_const_two :
    (fun _ : Fin 4 => (0 : Q3)) ≠ (fun _ : Fin 4 => (2 : Q3)) := by
  decide

theorem const_two_ne_const_zero :
    (fun _ : Fin 4 => (2 : Q3)) ≠ (fun _ : Fin 4 => (0 : Q3)) := by
  decide

theorem const_one_ne_const_two :
    (fun _ : Fin 4 => (1 : Q3)) ≠ (fun _ : Fin 4 => (2 : Q3)) := by
  decide

theorem const_two_ne_const_one :
    (fun _ : Fin 4 => (2 : Q3)) ≠ (fun _ : Fin 4 => (1 : Q3)) := by
  decide

theorem exWeight_nonneg : ∀ c : C4, 0 ≤ exWeight c := by
  intro c
  unfold exWeight
  split_ifs <;> positivity

theorem exWeight_sum_one : (∑ c : C4, exWeight c) = 1 := by
  simp [exWeight, Fin.sum_univ_succ]
  ring

noncomputable def exGame : FiniteFourPlayerXORGame Q3 :=
  FiniteFourPlayerXORGame.ofIndexed exQuery exSign exWeight
    exWeight_nonneg exWeight_sum_one

/-- Indices `0` and `1` are duplicates of the same signed tuple, so their
weights merge to `2/3`. -/
example : exGame.weight
    ((fun _ : Fin 4 => (0 : Q3)), (0 : ZMod 2)) = (2 / 3 : ℝ) := by
  simp [exGame, FiniteFourPlayerXORGame.ofIndexed_weight,
    exQuery_zero, exQuery_one, exQuery_two, exQuery_three,
    exSign_zero, exSign_one, exSign_two, exSign_three,
    exWeight_zero, exWeight_one, exWeight_two, exWeight_three,
    const_zero_ne_const_one, const_one_ne_const_zero,
    const_zero_ne_const_two, const_two_ne_const_zero,
    const_one_ne_const_two, const_two_ne_const_one,
    Fin.sum_univ_succ]
  ring

/-- The merged duplicate is in the support. -/
example :
    ((fun _ : Fin 4 => (0 : Q3)), (0 : ZMod 2)) ∈ exGame.support := by
  rw [FiniteFourPlayerXORGame.mem_support_iff]
  simp [exGame, FiniteFourPlayerXORGame.ofIndexed_weight,
    exQuery_zero, exQuery_one, exQuery_two, exQuery_three,
    exSign_zero, exSign_one, exSign_two, exSign_three,
    exWeight_zero, exWeight_one, exWeight_two, exWeight_three,
    const_zero_ne_const_one, const_one_ne_const_zero,
    const_zero_ne_const_two, const_two_ne_const_zero,
    const_one_ne_const_two, const_two_ne_const_one,
    Fin.sum_univ_succ]

/-- The zero-weight index does not put its signed tuple in the support. -/
example :
    ((fun _ : Fin 4 => (2 : Q3)), (1 : ZMod 2)) ∉ exGame.support := by
  rw [FiniteFourPlayerXORGame.mem_support_iff]
  simp [exGame, FiniteFourPlayerXORGame.ofIndexed_weight,
    exQuery_zero, exQuery_one, exQuery_two, exQuery_three,
    exSign_zero, exSign_one, exSign_two, exSign_three,
    exWeight_zero, exWeight_one, exWeight_two, exWeight_three,
    const_zero_ne_const_one, const_one_ne_const_zero,
    const_zero_ne_const_two, const_two_ne_const_zero,
    const_one_ne_const_two, const_two_ne_const_one,
    Fin.sum_univ_succ]

end FiniteGameExamples

end

end XORGame
end QIT

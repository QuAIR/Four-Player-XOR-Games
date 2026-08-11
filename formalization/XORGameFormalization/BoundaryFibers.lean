/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.CircuitCore
public import XORGameFormalization.RankBoundary

/-!
# Question-fiber structure at the nine- and ten-clause boundary

Question fibers partition a circuit support.  Fullness excludes singleton
fibers, while the adaptive rank bound forces three used questions on every
ten-clause page and on each ternary nine-clause page.  Hence every such
fiber has size in `2..6` or `2..5`, respectively.

A size-two fiber also forces its two integer-relation coefficients to be
opposites.  This is the algebraic source of the selected matching edges in
the boundary structural proof.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- The question fibers on one player page partition the clause support. -/
theorem sum_questionFiber_card
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (player : Fin 4) :
    ∑ question : Fin 3, (questionFiber query player question).card =
      Fintype.card E := by
  classical
  symm
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise
      (s := (Finset.univ : Finset E))
      (t := (Finset.univ : Finset (Fin 3)))
      (f := fun clause => query clause player)
      (by
        intro clause _
        exact Finset.mem_univ (query clause player))
  simpa [questionFiber] using hpartition

/-- A used question has a nonempty question fiber. -/
theorem questionFiber_card_pos_of_mem_usedQuestions
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (player : Fin 4)
    (question : Fin 3)
    (hused : question ∈ usedQuestions query player) :
    0 < (questionFiber query player question).card := by
  classical
  rw [Finset.card_pos]
  obtain ⟨clause, hclause⟩ :=
    (mem_usedQuestions query player question).mp hused
  exact ⟨clause, by simp [questionFiber, hclause]⟩

/--
Every used question fiber of a full circuit contains at least two clauses.
-/
theorem fullCircuit_usedQuestionFiber_card_two_le
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (player : Fin 4) (question : Fin 3)
    (hused : question ∈ usedQuestions query player) :
    2 ≤ (questionFiber query player question).card := by
  have hpositive :=
    questionFiber_card_pos_of_mem_usedQuestions
      query player question hused
  have hnotOne :=
    fullCircuit_questionFiber_card_ne_one
      query hCircuit player question
  omega

/-- Using all three questions means every question lies in the used set. -/
theorem mem_usedQuestions_of_card_three
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (player : Fin 4)
    (hcard : usedQuestionsCard query player = 3)
    (question : Fin 3) :
    question ∈ usedQuestions query player := by
  classical
  have hall :
      usedQuestions query player = (Finset.univ : Finset (Fin 3)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa [usedQuestionsCard] using hcard.ge
  rw [hall]
  exact Finset.mem_univ question

/--
On a ternary page of a nine-clause full circuit, every question fiber has
between two and five clauses.
-/
theorem nineClause_ternaryFullCircuit_questionFiber_bounds
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (player : Fin 4)
    (hternary : usedQuestionsCard query player = 3) :
    ∀ question : Fin 3,
      2 ≤ (questionFiber query player question).card ∧
        (questionFiber query player question).card ≤ 5 := by
  have hlower :
      ∀ question : Fin 3,
        2 ≤ (questionFiber query player question).card :=
    fun question =>
      fullCircuit_usedQuestionFiber_card_two_le
        query hCircuit player question
        (mem_usedQuestions_of_card_three
          query player hternary question)
  have hsum := sum_questionFiber_card query player
  rw [hcard] at hsum
  simp only [Fin.sum_univ_succ] at hsum
  norm_num [Fin.ext_iff] at hsum
  intro question
  constructor
  · exact hlower question
  · have hzero := hlower (0 : Fin 3)
    have hone := hlower (1 : Fin 3)
    have htwo := hlower (2 : Fin 3)
    have hcases :
        question = (0 : Fin 3) ∨
          question = (1 : Fin 3) ∨
            question = (2 : Fin 3) := by
      fin_cases question <;> simp [Fin.ext_iff]
    rcases hcases with hq | hq | hq <;> subst question <;> omega

/--
Every question fiber of a ten-clause full circuit has between two and six
clauses.
-/
theorem tenClause_fullCircuit_questionFiber_bounds
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 10)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    ∀ player : Fin 4, ∀ question : Fin 3,
      2 ≤ (questionFiber query player question).card ∧
        (questionFiber query player question).card ≤ 6 := by
  intro player
  have hternary :=
    tenClause_fullCircuit_uses_all_questions
      query hcard hCircuit player
  have hlower :
      ∀ question : Fin 3,
        2 ≤ (questionFiber query player question).card :=
    fun question =>
      fullCircuit_usedQuestionFiber_card_two_le
        query hCircuit player question
        (mem_usedQuestions_of_card_three
          query player hternary question)
  have hsum := sum_questionFiber_card query player
  rw [hcard] at hsum
  simp only [Fin.sum_univ_succ] at hsum
  norm_num [Fin.ext_iff] at hsum
  intro question
  constructor
  · exact hlower question
  · have hzero := hlower (0 : Fin 3)
    have hone := hlower (1 : Fin 3)
    have htwo := hlower (2 : Fin 3)
    have hcases :
        question = (0 : Fin 3) ∨
          question = (1 : Fin 3) ∨
            question = (2 : Fin 3) := by
      fin_cases question <;> simp [Fin.ext_iff]
    rcases hcases with hq | hq | hq <;> subst question <;> omega

/--
An integer relation on a two-clause question fiber has opposite
coefficients at the two clauses.
-/
theorem integerRelation_coefficients_neg_of_questionFiber_eq_pair
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (player : Fin 4) (question : Fin 3)
    (clause₁ clause₂ : E) (hne : clause₁ ≠ clause₂)
    (hpair : questionFiber query player question = {clause₁, clause₂}) :
    y clause₁ = -y clause₂ := by
  classical
  have hfiber_iff (clause : E) :
      query clause player = question ↔
        clause = clause₁ ∨ clause = clause₂ := by
    have hmem :=
      congrArg (fun fiber : Finset E => clause ∈ fiber) hpair
    simpa [questionFiber] using hmem
  have hrelation := hy (player, question)
  have hfiltered :
      ∑ clause ∈ questionFiber query player question, y clause = 0 := by
    rw [questionFiber, Finset.sum_filter]
    simpa [incidence, hfiber_iff] using hrelation
  rw [hpair] at hfiltered
  have hsum : y clause₁ + y clause₂ = 0 := by
    simpa [hne] using hfiltered
  omega

end

end XORGame
end QIT

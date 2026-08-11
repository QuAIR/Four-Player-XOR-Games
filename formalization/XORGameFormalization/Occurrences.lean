/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Signed clause occurrences and question-preserving matchings

An integer incidence relation contains `(y c).toNat` positive copies and
`(-y c).toNat` negative copies of every clause `c`.  In each fixed
player-question block, the relation equation says that the two finite
occurrence sets have the same cardinality.  We turn those equalities into a
question-preserving perfect matching for every player.

This is the structural matching object used by the noncrossing-order and
small-circuit arguments; it is stronger and more reusable than a bare
coordinatewise sum identity.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- The finite set of positive copies of an integer coefficient vector. -/
abbrev PositiveOccurrence (y : ClauseId → ℤ) :=
  Σ clause : ClauseId, Fin (y clause).toNat

/-- The finite set of negative copies of an integer coefficient vector. -/
abbrev NegativeOccurrence (y : ClauseId → ℤ) :=
  Σ clause : ClauseId, Fin (-y clause).toNat

/-- The question seen by a positive occurrence at one player. -/
def positiveOccurrenceQuestion
    (query : ClauseId → Clause Player Question) (player : Player)
    {y : ClauseId → ℤ} (occurrence : PositiveOccurrence y) : Question :=
  query occurrence.1 player

/-- The question seen by a negative occurrence at one player. -/
def negativeOccurrenceQuestion
    (query : ClauseId → Clause Player Question) (player : Player)
    {y : ClauseId → ℤ} (occurrence : NegativeOccurrence y) : Question :=
  query occurrence.1 player

private def positiveOccurrenceFiberEquiv
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (player : Player) (question : Question) :
    {occurrence : PositiveOccurrence y //
      positiveOccurrenceQuestion query player occurrence = question} ≃
      Σ clause : {clause : ClauseId // query clause player = question},
        Fin (y clause.1).toNat := {
  toFun occurrence :=
    ⟨⟨occurrence.1.1, occurrence.2⟩, occurrence.1.2⟩
  invFun occurrence :=
    ⟨⟨occurrence.1.1, occurrence.2⟩, occurrence.1.2⟩
  left_inv occurrence := by
    rcases occurrence with ⟨⟨clause, copy⟩, hquestion⟩
    rfl
  right_inv occurrence := by
    rcases occurrence with ⟨⟨clause, hquestion⟩, copy⟩
    rfl
}

private def negativeOccurrenceFiberEquiv
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (player : Player) (question : Question) :
    {occurrence : NegativeOccurrence y //
      negativeOccurrenceQuestion query player occurrence = question} ≃
      Σ clause : {clause : ClauseId // query clause player = question},
        Fin (-y clause.1).toNat := {
  toFun occurrence :=
    ⟨⟨occurrence.1.1, occurrence.2⟩, occurrence.1.2⟩
  invFun occurrence :=
    ⟨⟨occurrence.1.1, occurrence.2⟩, occurrence.1.2⟩
  left_inv occurrence := by
    rcases occurrence with ⟨⟨clause, copy⟩, hquestion⟩
    rfl
  right_inv occurrence := by
    rcases occurrence with ⟨⟨clause, hquestion⟩, copy⟩
    rfl
}

/-- Cardinality of the positive occurrences in one player-question block. -/
theorem positiveOccurrenceQuestion_fiber_card
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (player : Player) (question : Question) :
    Fintype.card
        {occurrence : PositiveOccurrence y //
          positiveOccurrenceQuestion query player occurrence = question} =
      ∑ clause : ClauseId,
        if query clause player = question then (y clause).toNat else 0 := by
  rw [Fintype.card_congr
    (positiveOccurrenceFiberEquiv query y player question),
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ clause : {clause : ClauseId //
        query clause player = question}, (y clause.1).toNat) =
        ∑ clause ∈ Finset.univ.filter
            (fun clause => query clause player = question),
          (y clause).toNat := by
      symm
      apply Finset.sum_subtype
      intro clause
      simp
    _ = ∑ clause : ClauseId,
        if query clause player = question then (y clause).toNat else 0 := by
      rw [Finset.sum_filter]

/-- Cardinality of the negative occurrences in one player-question block. -/
theorem negativeOccurrenceQuestion_fiber_card
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (player : Player) (question : Question) :
    Fintype.card
        {occurrence : NegativeOccurrence y //
          negativeOccurrenceQuestion query player occurrence = question} =
      ∑ clause : ClauseId,
        if query clause player = question then (-y clause).toNat else 0 := by
  rw [Fintype.card_congr
    (negativeOccurrenceFiberEquiv query y player question),
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    (∑ clause : {clause : ClauseId //
        query clause player = question}, (-y clause.1).toNat) =
        ∑ clause ∈ Finset.univ.filter
            (fun clause => query clause player = question),
          (-y clause).toNat := by
      symm
      apply Finset.sum_subtype
      intro clause
      simp
    _ = ∑ clause : ClauseId,
        if query clause player = question then (-y clause).toNat else 0 := by
      rw [Finset.sum_filter]

/--
Every integer relation has equally many positive and negative occurrences in
each player-question block.
-/
theorem positiveMultiplicity_eq_negativeMultiplicity_in_questionFiber
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hy : IsIntegerRelation query y)
    (player : Player) (question : Question) :
    (∑ clause : ClauseId,
        if query clause player = question then (y clause).toNat else 0) =
      ∑ clause : ClauseId,
        if query clause player = question then (-y clause).toNat else 0 := by
  have hrelation :
      (∑ clause : ClauseId,
        if query clause player = question then y clause else 0) = 0 := by
    simpa [incidence] using hy (player, question)
  have hsub :
      (∑ clause : ClauseId,
          if query clause player = question then
            ((y clause).toNat : ℤ)
          else 0) -
        (∑ clause : ClauseId,
          if query clause player = question then
            ((-y clause).toNat : ℤ)
          else 0) = 0 := by
    calc
      _ = ∑ clause : ClauseId,
          if query clause player = question then
            ((y clause).toNat : ℤ) - ((-y clause).toNat : ℤ)
          else 0 := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro clause _
        split <;> simp
      _ = ∑ clause : ClauseId,
          if query clause player = question then y clause else 0 := by
        apply Finset.sum_congr rfl
        intro clause _
        split
        · simp only [Int.toNat_sub_toNat_neg]
        · simp
      _ = 0 := hrelation
  apply Int.ofNat_inj.mp
  simpa using sub_eq_zero.mp hsub

/--
The positive and negative occurrence fibers have the same size for every
player and question.
-/
theorem positiveOccurrenceQuestion_fiber_card_eq_negative
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hy : IsIntegerRelation query y)
    (player : Player) (question : Question) :
    Fintype.card
        {occurrence : PositiveOccurrence y //
          positiveOccurrenceQuestion query player occurrence = question} =
      Fintype.card
        {occurrence : NegativeOccurrence y //
          negativeOccurrenceQuestion query player occurrence = question} := by
  rw [positiveOccurrenceQuestion_fiber_card,
    negativeOccurrenceQuestion_fiber_card]
  exact positiveMultiplicity_eq_negativeMultiplicity_in_questionFiber
    query y hy player question

/--
For every player, an integer incidence relation canonically supplies a
question-preserving perfect matching from positive to negative occurrences.

The choice inside each question fiber is noncomputable and intentionally
arbitrary: later structural theorems reason about the existence of such
matchings, not a particular enumeration.
-/
noncomputable def occurrenceMatchingForPlayer
    [Fintype ClauseId] [Fintype Question] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hy : IsIntegerRelation query y) (player : Player) :
    PositiveOccurrence y ≃ NegativeOccurrence y :=
  Equiv.ofFiberEquiv
    (f := positiveOccurrenceQuestion query player)
    (g := negativeOccurrenceQuestion query player)
    (fun question =>
      Fintype.equivOfCardEq
        (positiveOccurrenceQuestion_fiber_card_eq_negative
          query y hy player question))

/-- The occurrence matching for a player preserves that player's question. -/
theorem occurrenceMatchingForPlayer_preserves_question
    [Fintype ClauseId] [Fintype Question] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ)
    (hy : IsIntegerRelation query y) (player : Player)
    (occurrence : PositiveOccurrence y) :
    positiveOccurrenceQuestion query player occurrence =
      negativeOccurrenceQuestion query player
        (occurrenceMatchingForPlayer query y hy player occurrence) := by
  symm
  exact Equiv.ofFiberEquiv_map _ occurrence

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.BinaryPage
public import XORGameFormalization.BipartiteForestLayout
public import XORGameFormalization.AdjacentPairDeletion
public import XORGameFormalization.SharedBlockLift

/-!
# Selected-block linear-forest occurrence layouts

This module applies the abstract bipartite linear-forest theorem to signed
clause occurrences.  It is the graph-to-word bridge used by the shared-block
and three-ternary-page reductions.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uE

noncomputable section

/-- The selected-block simple graph is bipartite in the occurrence signs. -/
theorem selectedBlockSimpleGraph_oppositeSign
    {Player : Type uP} {Positive : Type*} {Negative : Type*}
    (Match : Player → Positive → Negative → Prop)
    {left right : Positive ⊕ Negative}
    (hadj : (selectedBlockSimpleGraph Match).Adj left right) :
    OppositeSign left right := by
  cases left <;> cases right <;>
    simp [selectedBlockSimpleGraph, OppositeSign] at hadj ⊢

/--
An integer relation supplies equally many positive and negative signed
occurrences (use any player and sum its question fibres).
-/
theorem positiveOccurrence_card_eq_negativeOccurrence
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Nonempty Player] [Fintype Question] [Fintype E]
    [DecidableEq Question]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y) :
    Fintype.card (PositiveOccurrence y) =
      Fintype.card (NegativeOccurrence y) := by
  let player : Player := Classical.choice inferInstance
  exact Fintype.card_congr
    (occurrenceMatchingForPlayer query y hy player)

/--
The selected-block certificate has a complete sign-alternating occurrence
order in which every selected matching edge is adjacent.
-/
theorem selectedBlockLinearForest_alternatingLayout
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Nonempty Player] [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : SelectedBlockLinearForestCertificate query y) :
    Nonempty
      (BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match)) := by
  classical
  apply exists_bipartiteLinearForestAlternatingLayout
  · exact certificate.linear_forest.1
  · intro vertex
    rw [← (selectedBlockSimpleGraph certificate.Match).card_neighborSet_eq_degree,
      Set.fintypeCard_eq_ncard]
    exact certificate.linear_forest.2 vertex
  · intro left right hadj
    exact selectedBlockSimpleGraph_oppositeSign certificate.Match hadj
  · exact positiveOccurrence_card_eq_negativeOccurrence query y hy

/-- The complete alternating layout is a complete signed-occurrence order. -/
theorem bipartiteLinearForestLayout_isCompleteOccurrenceOrder
    {E : Type uE} [Fintype E] [DecidableEq E]
    {y : E → ℤ}
    {G : SimpleGraph (SignedOccurrence y)}
    (layout : BipartiteLinearForestAlternatingLayout G) :
    IsCompleteOccurrenceOrder y layout.order := by
  classical
  letI : BEq (SignedOccurrence y) :=
    ⟨fun left right => decide (left = right)⟩
  unfold IsCompleteOccurrenceOrder
  rw [List.perm_iff_count]
  intro occurrence
  have hleftPos : 0 < layout.order.count occurrence :=
    List.count_pos_iff.mpr (layout.complete occurrence)
  have hleftLe : layout.order.count occurrence ≤ 1 :=
    List.nodup_iff_count_le_one.mp layout.nodup occurrence
  have hrightMem :
      occurrence ∈ (Finset.univ.toList : List (SignedOccurrence y)) := by
    simp
  have hrightPos :
      0 < (Finset.univ.toList : List (SignedOccurrence y)).count occurrence :=
    List.count_pos_iff.mpr hrightMem
  have hrightLe :
      (Finset.univ.toList : List (SignedOccurrence y)).count occurrence ≤ 1 :=
    List.nodup_iff_count_le_one.mp (Finset.nodup_toList _) occurrence
  omega

/-- Whether a signed occurrence lies in the selected question block. -/
def IsSelectedOccurrence
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) (occurrence : SignedOccurrence y) : Prop :=
  signedOccurrenceQuestion query player occurrence =
    certificate.selectedQuestion player

/-- Symmetric mate relation induced by one player's selected matching. -/
def SelectedOccurrenceMate
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) :
    SignedOccurrence y → SignedOccurrence y → Prop
  | Sum.inl positive, Sum.inr negative =>
      certificate.Match player positive negative
  | Sum.inr negative, Sum.inl positive =>
      certificate.Match player positive negative
  | _, _ => False

/-- The one-player selected mate relation is symmetric. -/
theorem selectedOccurrenceMate_symm
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) {left right : SignedOccurrence y}
    (hmate : SelectedOccurrenceMate query y certificate player left right) :
    SelectedOccurrenceMate query y certificate player right left := by
  cases left <;> cases right <;>
    simpa [SelectedOccurrenceMate] using hmate

/-- A selected mate always has the opposite occurrence sign. -/
theorem selectedOccurrenceMate_ne
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) {left right : SignedOccurrence y}
    (hmate : SelectedOccurrenceMate query y certificate player left right) :
    left ≠ right := by
  cases left <;> cases right <;>
    simp_all [SelectedOccurrenceMate]

/-- Both endpoints of a selected mate edge lie in the selected block. -/
theorem selectedOccurrenceMate_isSelected
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) {left right : SignedOccurrence y}
    (hmate : SelectedOccurrenceMate query y certificate player left right) :
    IsSelectedOccurrence query y certificate player left ∧
      IsSelectedOccurrence query y certificate player right := by
  cases left with
  | inl positive =>
      cases right with
      | inl other => simp [SelectedOccurrenceMate] at hmate
      | inr negative =>
          exact certificate.match_mem hmate
  | inr negative =>
      cases right with
      | inl positive =>
          exact (certificate.match_mem hmate).symm
      | inr other => simp [SelectedOccurrenceMate] at hmate

/-- Selected mate endpoints have the same question label on that page. -/
theorem selectedOccurrenceMate_question_eq
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) {left right : SignedOccurrence y}
    (hmate : SelectedOccurrenceMate query y certificate player left right) :
    signedOccurrenceQuestion query player left =
      signedOccurrenceQuestion query player right := by
  have hselected :=
    selectedOccurrenceMate_isSelected
      query y certificate player hmate
  exact hselected.1.trans hselected.2.symm

/-- The one-player selected mate is unique at either endpoint. -/
theorem selectedOccurrenceMate_functional
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (player : Player) {vertex first second : SignedOccurrence y}
    (hfirst :
      SelectedOccurrenceMate query y certificate player vertex first)
    (hsecond :
      SelectedOccurrenceMate query y certificate player vertex second) :
    first = second := by
  cases vertex with
  | inl positive =>
      cases first with
      | inl other => simp [SelectedOccurrenceMate] at hfirst
      | inr firstNegative =>
          cases second with
          | inl other => simp [SelectedOccurrenceMate] at hsecond
          | inr secondNegative =>
              congr 1
              exact
                (certificate.positive_unique player positive
                  (certificate.match_mem hfirst).1).unique hfirst hsecond
  | inr negative =>
      cases first with
      | inl firstPositive =>
          cases second with
          | inl secondPositive =>
              congr 1
              exact
                (certificate.negative_unique player negative
                  (certificate.match_mem hfirst).2).unique hfirst hsecond
          | inr other => simp [SelectedOccurrenceMate] at hsecond
      | inr other => simp [SelectedOccurrenceMate] at hfirst

/--
On each player page, the selected occurrences appear as disjoint adjacent
equal-question pairs in the forest layout.
-/
theorem selectedBlockLinearForest_adjacentSelectedPairing
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (layout :
      BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match))
    (player : Player) :
    InvolutionWord.AdjacentSelectedPairing
      (IsSelectedOccurrence query y certificate player)
      (signedOccurrenceQuestion query player) layout.order := by
  classical
  apply InvolutionWord.adjacentSelectedPairing_of_unique_adjacent_mates
    (IsSelectedOccurrence query y certificate player)
    (signedOccurrenceQuestion query player)
    (SelectedOccurrenceMate query y certificate player)
  · exact selectedOccurrenceMate_symm query y certificate player
  · exact selectedOccurrenceMate_ne query y certificate player
  · exact selectedOccurrenceMate_isSelected query y certificate player
  · exact selectedOccurrenceMate_question_eq query y certificate player
  · exact selectedOccurrenceMate_functional query y certificate player
  · exact layout.nodup
  · intro occurrence _hmem hselected
    cases occurrence with
    | inl positive =>
        obtain ⟨negative, hmatch, _⟩ :=
          certificate.positive_unique player positive hselected
        exact ⟨Sum.inr negative, layout.complete _, hmatch⟩
    | inr negative =>
        obtain ⟨positive, hmatch, _⟩ :=
          certificate.negative_unique player negative hselected
        exact ⟨Sum.inl positive, layout.complete _, hmatch⟩
  · intro left right _hleft _hright hmate
    apply layout.covers
    cases left with
    | inl positive =>
        cases right with
        | inl other => simp [SelectedOccurrenceMate] at hmate
        | inr negative => exact ⟨player, hmate⟩
    | inr negative =>
        cases right with
        | inl positive => exact ⟨player, hmate⟩
        | inr other => simp [SelectedOccurrenceMate] at hmate

/-- The sign of a signed occurrence, viewed as an integer. -/
def signedOccurrenceSign
    {Positive : Type*} {Negative : Type*} :
    Positive ⊕ Negative → ℤ
  | Sum.inl _ => 1
  | Sum.inr _ => -1

/-- Opposite occurrence signs have opposite integer signs. -/
theorem signedOccurrenceSign_eq_neg_of_oppositeSign
    {Positive : Type*} {Negative : Type*}
    {left right : Positive ⊕ Negative}
    (hopposite : OppositeSign left right) :
    signedOccurrenceSign right = -signedOccurrenceSign left := by
  cases left <;> cases right <;>
    simp_all [OppositeSign, signedOccurrenceSign]

/-- Every occurrence sign squares to one. -/
theorem signedOccurrenceSign_mul_self
    {Positive : Type*} {Negative : Type*}
    (occurrence : Positive ⊕ Negative) :
    signedOccurrenceSign occurrence * signedOccurrenceSign occurrence = 1 := by
  cases occurrence <;> simp [signedOccurrenceSign]

/--
Along an opposite-sign chain, positional alternating sum is the signed
vertex sum, up to the harmless sign of the first vertex.
-/
theorem alternatingSum_map_eq_headSign_mul_sum
    {Positive : Type*} {Negative : Type*} {Letter : Type*}
    (weight : Letter → ℤ) (label : Positive ⊕ Negative → Letter) :
    ∀ order : List (Positive ⊕ Negative),
      order.IsChain OppositeSign →
      InvolutionWord.alternatingSum weight (order.map label) =
        match order with
        | [] => 0
        | head :: _ =>
            signedOccurrenceSign head *
              (order.map fun occurrence =>
                signedOccurrenceSign occurrence *
                  weight (label occurrence)).sum
  | [], _hchain => by simp [InvolutionWord.alternatingSum]
  | [head], _hchain => by
      cases head <;>
        simp [InvolutionWord.alternatingSum, signedOccurrenceSign]
  | head :: next :: tail, hchain => by
      have ih :=
        alternatingSum_map_eq_headSign_mul_sum
          weight label (next :: tail) hchain.tail
      simp only [List.map_cons, InvolutionWord.alternatingSum,
        List.sum_cons] at ih ⊢
      rw [ih]
      cases head <;> cases next <;>
        simp_all [OppositeSign, signedOccurrenceSign] <;> ring

/--
For an integer relation, the total signed indicator weight of every
player-question fibre is zero.
-/
theorem signedOccurrenceQuestion_indicator_sum_eq_zero
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Question] [Fintype E] [DecidableEq Question]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (player : Player) (question : Question) :
    ∑ occurrence : SignedOccurrence y,
      signedOccurrenceSign occurrence *
        (if signedOccurrenceQuestion query player occurrence = question
          then 1 else 0) = 0 := by
  let matching := occurrenceMatchingForPlayer query y hy player
  have hsum :
      (∑ positive : PositiveOccurrence y,
          if positiveOccurrenceQuestion query player positive = question
            then (1 : ℤ) else 0) =
        ∑ negative : NegativeOccurrence y,
          if negativeOccurrenceQuestion query player negative = question
            then (1 : ℤ) else 0 := by
    apply Fintype.sum_equiv matching
    intro positive
    rw [occurrenceMatchingForPlayer_preserves_question
      query y hy player positive]
  have hsum' := hsum
  change
    (∑ positive : PositiveOccurrence y,
        if query positive.1 player = question then (1 : ℤ) else 0) =
      ∑ negative : NegativeOccurrence y,
        if query negative.1 player = question then (1 : ℤ) else 0 at hsum'
  rw [Fintype.sum_sum_type]
  simp only [signedOccurrenceSign, signedOccurrenceQuestion,
    signedOccurrenceClause, one_mul, neg_one_mul]
  rw [Finset.sum_neg_distrib]
  rw [← sub_eq_add_neg]
  exact sub_eq_zero.mpr hsum'

/--
A complete alternating occurrence order has zero positional alternating sum
in every player-question fibre.
-/
theorem completeAlternatingOccurrenceOrder_alternatingSum_eq_zero
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Question] [Fintype E]
    [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (player : Player) (question : Question)
    (order : List (SignedOccurrence y))
    (hcomplete : IsCompleteOccurrenceOrder y order)
    (halternating : order.IsChain OppositeSign) :
    InvolutionWord.alternatingSum
      (fun localQuestion => if localQuestion = question then 1 else 0)
      (order.map (signedOccurrenceQuestion query player)) = 0 := by
  have hformula := alternatingSum_map_eq_headSign_mul_sum
    (fun localQuestion => if localQuestion = question then 1 else 0)
    (signedOccurrenceQuestion query player) order halternating
  have hperm := hcomplete.map fun occurrence =>
    signedOccurrenceSign occurrence *
      (if signedOccurrenceQuestion query player occurrence = question
        then 1 else 0)
  have hsum :
      (order.map fun occurrence =>
        signedOccurrenceSign occurrence *
          (if signedOccurrenceQuestion query player occurrence = question
            then 1 else 0)).sum = 0 := by
    calc
      _ =
          ((Finset.univ.toList : List (SignedOccurrence y)).map
            fun occurrence =>
              signedOccurrenceSign occurrence *
                (if signedOccurrenceQuestion query player occurrence = question
                  then 1 else 0)).sum :=
        hperm.sum_eq
      _ =
          ∑ occurrence : SignedOccurrence y,
            signedOccurrenceSign occurrence *
              (if signedOccurrenceQuestion query player occurrence = question
                then 1 else 0) := by simp
      _ = 0 :=
        signedOccurrenceQuestion_indicator_sum_eq_zero
          query y hy player question
  cases order with
  | nil => simpa using hformula
  | cons head tail =>
      rw [hformula, hsum]
      simp

/-- Delete all signed occurrences in one player's selected question block. -/
noncomputable def selectedBlockResidualOrder
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (layout :
      BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match))
    (player : Player) : List (SignedOccurrence y) := by
  classical
  exact layout.order.filter fun occurrence =>
    decide (¬ IsSelectedOccurrence query y certificate player occurrence)

/--
After deleting one selected question block from a page with at most three
questions, at most two question labels remain.
-/
theorem selectedBlockLinearForest_residual_card_le_two
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (layout :
      BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match))
    (hquestions : Fintype.card Question ≤ 3)
    (player : Player) :
    (((selectedBlockResidualOrder
        query y certificate layout player).map
      (signedOccurrenceQuestion query player)).toFinset).card ≤ 2 := by
  classical
  let residual :=
    (selectedBlockResidualOrder
      query y certificate layout player).map
        (signedOccurrenceQuestion query player)
  have hsubset :
      residual.toFinset ⊆
        (Finset.univ.erase (certificate.selectedQuestion player) :
          Finset Question) := by
    intro question hquestion
    simp only [residual, selectedBlockResidualOrder,
      List.mem_toFinset, List.mem_map, List.mem_filter] at hquestion
    obtain ⟨occurrence, ⟨_hmem, hunselected⟩, rfl⟩ := hquestion
    have hunselected' :
        ¬ IsSelectedOccurrence query y certificate player occurrence :=
      of_decide_eq_true hunselected
    exact Finset.mem_erase.mpr
      ⟨by simpa [IsSelectedOccurrence] using hunselected', Finset.mem_univ _⟩
  calc
    residual.toFinset.card ≤
        (Finset.univ.erase
          (certificate.selectedQuestion player) : Finset Question).card :=
      Finset.card_le_card hsubset
    _ = Fintype.card Question - 1 := by simp
    _ ≤ 2 := by omega

/--
Deleting selected adjacent pairs preserves the zero alternating sum supplied
by the integer relation.
-/
theorem selectedBlockLinearForest_residual_alternatingSum_eq_zero
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (layout :
      BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match))
    (player : Player) (question : Question) :
    InvolutionWord.alternatingSum
      (fun localQuestion => if localQuestion = question then 1 else 0)
      ((selectedBlockResidualOrder
          query y certificate layout player).map
        (signedOccurrenceQuestion query player)) = 0 := by
  classical
  let pairing :=
    selectedBlockLinearForest_adjacentSelectedPairing
      query y certificate layout player
  have hextension :
      InvolutionWord.PairInsertionExtension
        ((selectedBlockResidualOrder
            query y certificate layout player).map
          (signedOccurrenceQuestion query player))
        (layout.order.map (signedOccurrenceQuestion query player)) := by
    simpa [selectedBlockResidualOrder] using
      pairing.pairInsertionExtension
  have heq := hextension.alternatingSum_eq
    (fun localQuestion => if localQuestion = question then 1 else 0)
  have hfull :=
    completeAlternatingOccurrenceOrder_alternatingSum_eq_zero
      query y hy player question layout.order
        (bipartiteLinearForestLayout_isCompleteOccurrenceOrder layout)
        layout.alternating
  exact heq.symm.trans hfull

/-- Every page word in a selected-block forest layout reduces to empty. -/
theorem selectedBlockLinearForest_question_reducesToEmpty
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (layout :
      BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match))
    (hquestions : Fintype.card Question ≤ 3)
    (player : Player) :
    InvolutionWord.ReducesToEmpty
      (layout.order.map (signedOccurrenceQuestion query player)) := by
  classical
  let pairing :=
    selectedBlockLinearForest_adjacentSelectedPairing
      query y certificate layout player
  have hresidual :
      InvolutionWord.ReducesToEmpty
        ((selectedBlockResidualOrder
            query y certificate layout player).map
          (signedOccurrenceQuestion query player)) := by
    apply
    InvolutionWord.reducesToEmpty_of_toFinset_card_le_two_of_alternatingSum_zero
    · exact selectedBlockLinearForest_residual_card_le_two
        query y certificate layout hquestions player
    · exact selectedBlockLinearForest_residual_alternatingSum_eq_zero
        query y hy certificate layout player
  have hextension :
      InvolutionWord.PairInsertionExtension
        ((selectedBlockResidualOrder
            query y certificate layout player).map
          (signedOccurrenceQuestion query player))
        (layout.order.map (signedOccurrenceQuestion query player)) := by
    simpa [selectedBlockResidualOrder] using
      pairing.pairInsertionExtension
  exact hextension.reducesToEmpty hresidual

/--
The selected-block linear-forest certificate gives an exact-multiplicity
balanced lift whenever every page alphabet has size at most three.
-/
theorem selectedBlockLinearForest_exactMultiplicityBalancedLift_of_card_le_three
    {Player : Type uP} {Question : Type uQ} {E : Type uE}
    [Nonempty Player] [Fintype Player] [Fintype Question] [Fintype E]
    [DecidableEq Player] [DecidableEq Question] [DecidableEq E]
    (query : E → Clause Player Question) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : SelectedBlockLinearForestCertificate query y)
    (hquestions : Fintype.card Question ≤ 3) :
    HasExactMultiplicityBalancedLift query y := by
  classical
  let layout := Classical.choice
    (selectedBlockLinearForest_alternatingLayout
      query y hy certificate)
  have hcomplete : IsCompleteOccurrenceOrder y layout.order :=
    bipartiteLinearForestLayout_isCompleteOccurrenceOrder layout
  refine ⟨layout.order.map signedOccurrenceClause, ?_, ?_⟩
  · intro player
    have hreduced := selectedBlockLinearForest_question_reducesToEmpty
      query y hy certificate layout hquestions player
    simpa [signedOccurrenceQuestion, List.map_map,
      Function.comp_def] using hreduced
  · intro clause
    exact completeOccurrenceOrder_clause_count
      y layout.order hcomplete clause

/-- Four players with three questions: the selected-block forest lift. -/
theorem selectedBlockLinearForest_exactMultiplicityBalancedLift
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : SelectedBlockLinearForestCertificate query y) :
    HasExactMultiplicityBalancedLift query y := by
  apply
    selectedBlockLinearForest_exactMultiplicityBalancedLift_of_card_le_three
      query y hy certificate
  simp [FourByThreeQuestion]

/--
The shared-third-question-block/missing-cell geometry is therefore a genuine
exact-lift escape, with no remaining layout hypothesis.
-/
theorem hasExactMultiplicityBalancedLift_of_sharedThirdQuestionBlockMissingCell
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (x yCenter : FourByThreeClause)
    (hshared :
      HasSharedThirdQuestionBlockMissingCell query x yCenter) :
    HasExactMultiplicityBalancedLift query y := by
  obtain ⟨certificate⟩ :=
    hasSelectedBlockLinearForestCertificate_of_sharedThirdQuestionBlockMissingCell
      query y hy x yCenter hshared
  exact selectedBlockLinearForest_exactMultiplicityBalancedLift
    query y hy certificate

/-- Restrict a four-by-three query to its ternary pages. -/
def ternaryPageQuery
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :
    E → Clause (TernaryPage query) FourByThreeQuestion :=
  fun clause player => query clause player.1

/-- Forget that a ternary-page forest certificate also records binary pages. -/
def TernaryPageLinearForestCertificate.toSelectedBlockCertificate
    {E : Type uE} [Fintype E]
    {query : E → FourByThreeClause} {y : E → ℤ}
    (certificate : TernaryPageLinearForestCertificate query y) :
    SelectedBlockLinearForestCertificate (ternaryPageQuery query) y where
  selectedQuestion := certificate.selectedQuestion
  Match := certificate.Match
  match_mem := certificate.match_mem
  positive_unique := certificate.positive_unique
  negative_unique := certificate.negative_unique
  linear_forest := certificate.linear_forest

/-- The ternary-page forest itself has a complete alternating layout. -/
theorem ternaryPageLinearForest_alternatingLayout
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (certificate : TernaryPageLinearForestCertificate query y) :
    Nonempty
      (BipartiteLinearForestAlternatingLayout
        (selectedBlockSimpleGraph certificate.Match)) := by
  classical
  apply exists_bipartiteLinearForestAlternatingLayout
  · exact certificate.linear_forest.1
  · intro vertex
    rw [← (selectedBlockSimpleGraph certificate.Match).card_neighborSet_eq_degree,
      Set.fintypeCard_eq_ncard]
    exact certificate.linear_forest.2 vertex
  · intro left right hadj
    exact selectedBlockSimpleGraph_oppositeSign certificate.Match hadj
  · exact positiveOccurrence_card_eq_negativeOccurrence query y hy

/-- Restricting an integer relation to a subtype of players preserves it. -/
theorem isIntegerRelation_ternaryPageQuery
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y) :
    IsIntegerRelation (ternaryPageQuery query) y := by
  intro playerQuestion
  exact hy (playerQuestion.1.1, playerQuestion.2)

/-- Every occurrence question in an arbitrary order is a used question. -/
theorem occurrenceQuestionWord_toFinset_card_le_usedQuestionsCard
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (order : List (SignedOccurrence y))
    (player : FourByThreePlayer) :
    ((order.map (signedOccurrenceQuestion query player)).toFinset).card ≤
      usedQuestionsCard query player := by
  apply Finset.card_le_card
  intro question hquestion
  simp only [List.mem_toFinset, List.mem_map] at hquestion
  obtain ⟨occurrence, _hmem, rfl⟩ := hquestion
  exact query_mem_usedQuestions
    query (signedOccurrenceClause occurrence) player

/--
At most three ternary pages imply an exact lift.  Ternary pages use the
selected-block deletion theorem; every other page goes directly through the
two-letter cancellation theorem.
-/
theorem hasExactMultiplicityBalancedLift_of_ternaryPlayers_card_le_three
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (hpages : (ternaryPlayers query).card ≤ 3)
    (hcard : Fintype.card E ≤ 26) :
    HasExactMultiplicityBalancedLift query y := by
  classical
  obtain ⟨certificate⟩ :=
    hasTernaryPageLinearForestCertificate_of_card_le_three
      query y hy hpages hcard
  obtain ⟨layout⟩ :=
    ternaryPageLinearForest_alternatingLayout query y hy certificate
  have hcomplete : IsCompleteOccurrenceOrder y layout.order :=
    bipartiteLinearForestLayout_isCompleteOccurrenceOrder layout
  refine ⟨layout.order.map signedOccurrenceClause, ?_, ?_⟩
  · intro player
    have hreduced :
        InvolutionWord.ReducesToEmpty
          (layout.order.map (signedOccurrenceQuestion query player)) := by
      by_cases hternary : player ∈ ternaryPlayers query
      · let ternaryPlayer : TernaryPage query := ⟨player, hternary⟩
        have hternaryReduced :=
          selectedBlockLinearForest_question_reducesToEmpty
            (ternaryPageQuery query) y
            (isIntegerRelation_ternaryPageQuery query y hy)
            certificate.toSelectedBlockCertificate layout
            (by simp [FourByThreeQuestion]) ternaryPlayer
        simpa [ternaryPlayer, ternaryPageQuery] using hternaryReduced
      · apply
          InvolutionWord.reducesToEmpty_of_toFinset_card_le_two_of_alternatingSum_zero
        · exact
            (occurrenceQuestionWord_toFinset_card_le_usedQuestionsCard
              query y layout.order player).trans
                (certificate.nonternary_card_le_two player hternary)
        · intro question
          exact
            completeAlternatingOccurrenceOrder_alternatingSum_eq_zero
              query y hy player question layout.order hcomplete
                layout.alternating
    simpa [signedOccurrenceQuestion, List.map_map,
      Function.comp_def] using hreduced
  · intro clause
    exact completeOccurrenceOrder_clause_count
      y layout.order hcomplete clause

end

end XORGame
end QIT

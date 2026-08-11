/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.HardCenterGeometry
public import XORGameFormalization.MatchingLift
public import XORGameFormalization.ThreeColorForest

/-!
# Shared-question-block forest certificates

This module formalizes the reduction from a shared complete question block
with a missing complementary cell to the three-color signature theorem.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
The three effective colors in the shared-block argument: one color for the
shared block, and one for each of the two complementary pages.
-/
abbrev SharedBlockColor
    (first second : FourByThreePlayer) :=
  Option (RemainingPlayers first second)

/-- The effective color signature of one clause. -/
def sharedBlockColorSignature
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (blockQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (clause : E) :
    Finset (SharedBlockColor first second) := by
  classical
  exact Finset.univ.filter fun color =>
    match color with
    | none => query clause first = blockQuestion
    | some player => query clause player.1 = cell player

@[simp]
theorem sharedBlockColor_card
    (first second : FourByThreePlayer)
    (hne : first ≠ second) :
    Fintype.card (SharedBlockColor first second) = 3 := by
  simp [SharedBlockColor, remainingPlayers_card first second hne]

@[simp]
theorem none_mem_sharedBlockColorSignature
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (blockQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (clause : E) :
    none ∈
        sharedBlockColorSignature query first second
          blockQuestion cell clause ↔
      query clause first = blockQuestion := by
  simp [sharedBlockColorSignature]

@[simp]
theorem some_mem_sharedBlockColorSignature
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (blockQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (clause : E) (player : RemainingPlayers first second) :
    some player ∈
        sharedBlockColorSignature query first second
          blockQuestion cell clause ↔
      query clause player.1 = cell player := by
  simp [sharedBlockColorSignature]

/-- Map each of the four pages to its effective shared-block color. -/
noncomputable def sharedBlockPageColor
    (first second : FourByThreePlayer)
    (player : FourByThreePlayer) :
    SharedBlockColor first second := by
  classical
  by_cases hfirst : player = first
  · exact none
  by_cases hsecond : player = second
  · exact none
  exact some ⟨player, hfirst, hsecond⟩

/-- The selected question on each page in the shared-block construction. -/
noncomputable def sharedBlockSelectedQuestion
    (first second : FourByThreePlayer)
    (firstQuestion secondQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (player : FourByThreePlayer) :
    FourByThreeQuestion := by
  classical
  by_cases hfirst : player = first
  · exact firstQuestion
  by_cases hsecond : player = second
  · exact secondQuestion
  exact cell ⟨player, hfirst, hsecond⟩

/--
Membership in the effective color at a page is exactly membership in that
page's selected question block.
-/
theorem sharedBlockPageColor_mem_signature_iff
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (firstQuestion secondQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (hshared :
      questionFiber query first firstQuestion =
        questionFiber query second secondQuestion)
    (clause : E) (player : FourByThreePlayer) :
    sharedBlockPageColor first second player ∈
        sharedBlockColorSignature query first second
          firstQuestion cell clause ↔
      query clause player =
        sharedBlockSelectedQuestion first second
          firstQuestion secondQuestion cell player := by
  classical
  by_cases hfirst : player = first
  · subst player
    simp [sharedBlockPageColor, sharedBlockSelectedQuestion]
  by_cases hsecond : player = second
  · subst player
    have hiff :
        query clause first = firstQuestion ↔
          query clause second = secondQuestion := by
      rw [← mem_questionFiber, ← mem_questionFiber, hshared]
    simpa [sharedBlockPageColor, sharedBlockSelectedQuestion,
      hfirst] using hiff
  · simp [sharedBlockPageColor, sharedBlockSelectedQuestion,
      hfirst, hsecond]

/--
An omitted complementary cell prevents any clause signature from containing
all three effective colors.
-/
theorem sharedBlockColorSignature_card_le_two_of_missing
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (hne : first ≠ second)
    (blockQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (hmissing :
      cell ∉
        (questionFiber query first blockQuestion).image
          (remainingQuestionProjection query first second))
    (clause : E) :
    (sharedBlockColorSignature query first second
      blockQuestion cell clause).card ≤ 2 := by
  by_contra hnot
  have hcardLe :
      (sharedBlockColorSignature query first second
        blockQuestion cell clause).card ≤
          Fintype.card (SharedBlockColor first second) :=
    Finset.card_le_univ _
  have hcard :
      (sharedBlockColorSignature query first second
        blockQuestion cell clause).card =
          Fintype.card (SharedBlockColor first second) := by
    rw [sharedBlockColor_card first second hne] at hcardLe ⊢
    omega
  have huniv :
      sharedBlockColorSignature query first second
          blockQuestion cell clause = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  apply hmissing
  apply Finset.mem_image.mpr
  refine ⟨clause, ?_, ?_⟩
  · rw [mem_questionFiber]
    have hnone :
        (none : SharedBlockColor first second) ∈
          sharedBlockColorSignature query first second
            blockQuestion cell clause := by
      rw [huniv]
      simp
    exact (none_mem_sharedBlockColorSignature
      query first second blockQuestion cell clause).mp hnone
  · funext player
    have hsome :
        (some player : SharedBlockColor first second) ∈
          sharedBlockColorSignature query first second
            blockQuestion cell clause := by
      rw [huniv]
      simp
    exact (some_mem_sharedBlockColorSignature
      query first second blockQuestion cell clause player).mp hsome

private theorem occurrenceQuestion_filter_card_eq
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (player : FourByThreePlayer)
    (question : FourByThreeQuestion) :
    (Finset.univ.filter
      (fun occurrence : PositiveOccurrence y =>
        query occurrence.1 player = question)).card =
      (Finset.univ.filter
        (fun occurrence : NegativeOccurrence y =>
          query occurrence.1 player = question)).card := by
  calc
    _ =
        Fintype.card
          {occurrence : PositiveOccurrence y //
            positiveOccurrenceQuestion query player occurrence =
              question} := by
      symm
      exact Fintype.card_ofFinset _ (by
        intro occurrence
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          positiveOccurrenceQuestion]
        rfl)
    _ =
        Fintype.card
          {occurrence : NegativeOccurrence y //
            negativeOccurrenceQuestion query player occurrence =
              question} :=
      positiveOccurrenceQuestion_fiber_card_eq_negative
        query y hy player question
    _ = _ := by
      exact Fintype.card_ofFinset _ (by
        intro occurrence
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          negativeOccurrenceQuestion]
        rfl)

/--
The occurrence signatures used in the shared-block reduction form a balanced
three-color signature system with signatures of size at most two.
-/
def sharedBlockColorSignatureSystem
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (first second : FourByThreePlayer)
    (hne : first ≠ second)
    (blockQuestion : FourByThreeQuestion)
    (cell : RemainingPlayers first second → FourByThreeQuestion)
    (hmissing :
      cell ∉
        (questionFiber query first blockQuestion).image
          (remainingQuestionProjection query first second)) :
    ColorSignatureSystem
      (SharedBlockColor first second)
      (PositiveOccurrence y) (NegativeOccurrence y) where
  positiveSignature occurrence :=
    sharedBlockColorSignature query first second
      blockQuestion cell occurrence.1
  negativeSignature occurrence :=
    sharedBlockColorSignature query first second
      blockQuestion cell occurrence.1
  positive_card_le_two occurrence :=
    sharedBlockColorSignature_card_le_two_of_missing
      query first second hne blockQuestion cell hmissing occurrence.1
  negative_card_le_two occurrence :=
    sharedBlockColorSignature_card_le_two_of_missing
      query first second hne blockQuestion cell hmissing occurrence.1
  balanced := by
    intro color
    cases color with
    | none =>
        simpa [sharedBlockColorSignature] using
          occurrenceQuestion_filter_card_eq
            query y hy first blockQuestion
    | some player =>
        simpa [sharedBlockColorSignature] using
          occurrenceQuestion_filter_card_eq
            query y hy player.1 (cell player)

/-- Simple union of selected-block matching edges over all player pages. -/
def selectedBlockSimpleGraph
    {Player : Type*} {Positive : Type*} {Negative : Type*}
    (Match : Player → Positive → Negative → Prop) :
    SimpleGraph (Positive ⊕ Negative) where
  Adj
    | Sum.inl positive, Sum.inr negative =>
        ∃ player, Match player positive negative
    | Sum.inr negative, Sum.inl positive =>
        ∃ player, Match player positive negative
    | _, _ => False
  symm := by
    intro left right hadj
    cases left <;> cases right <;> simpa using hadj
  loopless := by
    constructor
    intro vertex
    cases vertex <;> simp

/--
A selected question block and perfect matching on every page whose simple
union is a linear forest.
-/
structure SelectedBlockLinearForestCertificate
    {Player : Type*} {Question : Type*} {E : Type uE}
    [Fintype Player] [Fintype E]
    (query : E → Clause Player Question) (y : E → ℤ) where
  /-- The question block selected on each page. -/
  selectedQuestion : Player → Question
  /-- Matching edges in the selected block on each page. -/
  Match : Player → PositiveOccurrence y → NegativeOccurrence y → Prop
  /-- Every matching edge lies in the selected question block. -/
  match_mem :
    ∀ {player positive negative},
      Match player positive negative →
        query positive.1 player = selectedQuestion player ∧
          query negative.1 player = selectedQuestion player
  /-- Every eligible positive occurrence has exactly one partner. -/
  positive_unique :
    ∀ player positive,
      query positive.1 player = selectedQuestion player →
        ∃! negative, Match player positive negative
  /-- Every eligible negative occurrence has exactly one partner. -/
  negative_unique :
    ∀ player negative,
      query negative.1 player = selectedQuestion player →
        ∃! positive, Match player positive negative
  /-- The simple union has no cycle and maximum degree two. -/
  linear_forest :
    (selectedBlockSimpleGraph Match).IsAcyclic ∧
      ∀ vertex,
        ((selectedBlockSimpleGraph Match).neighborSet vertex).ncard ≤ 2

/-- Every effective shared-block color is represented by at least one page. -/
theorem sharedBlockPageColor_surjective
    (first second : FourByThreePlayer) :
    Function.Surjective (sharedBlockPageColor first second) := by
  intro color
  cases color with
  | none =>
      exact ⟨first, by
        simp [sharedBlockPageColor]⟩
  | some player =>
      refine ⟨player.1, ?_⟩
      simp [sharedBlockPageColor, player.2.1, player.2.2]

/-- Reindexing colors by a surjective page map does not change simple union. -/
theorem selectedBlockSimpleGraph_comp_surjective
    {Player : Type*} {Color : Type*}
    {Positive : Type*} {Negative : Type*}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]
    {system :
      ColorSignatureSystem Color Positive Negative}
    (matching : ColorwiseMatching system)
    (pageColor : Player → Color)
    (hpageColor : Function.Surjective pageColor) :
    selectedBlockSimpleGraph
        (fun player => matching.Match (pageColor player)) =
      matching.simpleGraph := by
  ext left right
  cases left with
  | inl positive =>
      cases right with
      | inl other =>
          simp [selectedBlockSimpleGraph,
            ColorwiseMatching.simpleGraph]
      | inr negative =>
          constructor
          · rintro ⟨player, hmatch⟩
            exact ⟨pageColor player, hmatch⟩
          · rintro ⟨color, hmatch⟩
            obtain ⟨player, rfl⟩ := hpageColor color
            exact ⟨player, hmatch⟩
  | inr negative =>
      cases right with
      | inl positive =>
          constructor
          · rintro ⟨player, hmatch⟩
            exact ⟨pageColor player, hmatch⟩
          · rintro ⟨color, hmatch⟩
            obtain ⟨player, rfl⟩ := hpageColor color
            exact ⟨player, hmatch⟩
      | inr other =>
          simp [selectedBlockSimpleGraph,
            ColorwiseMatching.simpleGraph]

/--
The shared-block/missing-cell geometry supplies an explicit selected-block
linear-forest certificate on all four pages, up to the universal
linear-forest-to-layout conversion.
-/
theorem hasSelectedBlockLinearForestCertificate_of_sharedThirdQuestionBlockMissingCell
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (x yCenter : FourByThreeClause)
    (hshared :
      HasSharedThirdQuestionBlockMissingCell query x yCenter) :
    Nonempty (SelectedBlockLinearForestCertificate query y) := by
  classical
  obtain ⟨first, second, hne, _hfirstDiffer, _hsecondDiffer,
      _hoff, hfibers, _hblockNonempty, _hblockCard,
      cell, hmissing⟩ := hshared
  let firstQuestion :=
    thirdQuestionValue (x first) (yCenter first)
  let secondQuestion :=
    thirdQuestionValue (x second) (yCenter second)
  let system :=
    sharedBlockColorSignatureSystem query y hy first second hne
      firstQuestion cell hmissing
  obtain ⟨matching, hforest⟩ :=
    threeColor_colorwiseMatching_linearForest system
      (by simpa [sharedBlockColor_card first second hne])
  let pageColor :=
    sharedBlockPageColor first second
  let selectedQuestion :=
    sharedBlockSelectedQuestion first second
      firstQuestion secondQuestion cell
  let Match :
      FourByThreePlayer →
        PositiveOccurrence y → NegativeOccurrence y → Prop :=
    fun player => matching.Match (pageColor player)
  refine ⟨{
    selectedQuestion := selectedQuestion
    Match := Match
    match_mem := ?_
    positive_unique := ?_
    negative_unique := ?_
    linear_forest := ?_
  }⟩
  · intro player positive negative hmatch
    have hmem := matching.match_mem hmatch
    refine ⟨?_, ?_⟩
    · exact
        (sharedBlockPageColor_mem_signature_iff
          query first second firstQuestion secondQuestion cell
          hfibers positive.1 player).mp hmem.1
    · exact
        (sharedBlockPageColor_mem_signature_iff
          query first second firstQuestion secondQuestion cell
          hfibers negative.1 player).mp hmem.2
  · intro player positive hpositive
    apply matching.positive_unique
    exact
      (sharedBlockPageColor_mem_signature_iff
        query first second firstQuestion secondQuestion cell
        hfibers positive.1 player).mpr hpositive
  · intro player negative hnegative
    apply matching.negative_unique
    exact
      (sharedBlockPageColor_mem_signature_iff
        query first second firstQuestion secondQuestion cell
        hfibers negative.1 player).mpr hnegative
  · have hgraph :
        selectedBlockSimpleGraph Match =
          matching.simpleGraph := by
      exact selectedBlockSimpleGraph_comp_surjective
        matching pageColor
          (sharedBlockPageColor_surjective first second)
    constructor
    · rw [hgraph]
      exact hforest.1
    · intro vertex
      rw [hgraph, ← Set.fintypeCard_eq_ncard,
        matching.simpleGraph.card_neighborSet_eq_degree]
      exact hforest.2 vertex

/-- The subtype of pages using all three local questions. -/
abbrev TernaryPage
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :=
  {player : FourByThreePlayer // player ∈ ternaryPlayers query}

/-- Restrict one clause to the ternary pages. -/
def ternaryPageProjection
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (clause : E) :
    TernaryPage query → FourByThreeQuestion :=
  fun player => query clause player.1

/-- Signature recording agreement with one selected ternary-page tuple. -/
def ternaryPageColorSignature
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (selected : TernaryPage query → FourByThreeQuestion)
    (clause : E) :
    Finset (TernaryPage query) :=
  Finset.univ.filter fun player =>
    query clause player.1 = selected player

/--
For at most three ternary pages one can select a tuple such that either
there are already at most two colors, or the selected triple is omitted by
the clause projection.
-/
theorem exists_ternaryPageSelection_with_small_or_missing
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hpages : (ternaryPlayers query).card ≤ 3)
    (hcard : Fintype.card E ≤ 26) :
    ∃ selected : TernaryPage query → FourByThreeQuestion,
      Fintype.card (TernaryPage query) ≤ 2 ∨
        (Fintype.card (TernaryPage query) = 3 ∧
          selected ∉
            Finset.univ.image (ternaryPageProjection query)) := by
  classical
  by_cases hsmall : Fintype.card (TernaryPage query) ≤ 2
  · exact ⟨fun _ => 0, Or.inl hsmall⟩
  have hpageCard :
      Fintype.card (TernaryPage query) = 3 := by
    rw [Fintype.card_coe]
    rw [Fintype.card_coe] at hsmall
    omega
  let projected :=
    Finset.univ.image (ternaryPageProjection query)
  have hprojectedCard :
      projected.card ≤ 26 := by
    exact (Finset.card_image_le.trans (by
      rw [Finset.card_univ]
      exact hcard))
  have htupleCard :
      Fintype.card
        (TernaryPage query → FourByThreeQuestion) = 27 := by
    rw [Fintype.card_fun, hpageCard]
    norm_num
  have hlt :
      projected.card <
        (Finset.univ :
          Finset
            (TernaryPage query → FourByThreeQuestion)).card := by
    rw [Finset.card_univ, htupleCard]
    omega
  obtain ⟨selected, _hselectedUniv, hselectedMissing⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨selected, Or.inr ⟨hpageCard, hselectedMissing⟩⟩

/-- The selected ternary-page tuple gives signatures of size at most two. -/
theorem ternaryPageColorSignature_card_le_two
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (selected : TernaryPage query → FourByThreeQuestion)
    (hselection :
      Fintype.card (TernaryPage query) ≤ 2 ∨
        (Fintype.card (TernaryPage query) = 3 ∧
          selected ∉
            Finset.univ.image (ternaryPageProjection query)))
    (clause : E) :
    (ternaryPageColorSignature query selected clause).card ≤ 2 := by
  classical
  rcases hselection with hsmall | ⟨hpageCard, hmissing⟩
  · exact
      (Finset.card_le_card
        (Finset.subset_univ
          (ternaryPageColorSignature query selected clause))).trans <|
        by simpa using hsmall
  · by_contra hnot
    have hsignatureLe :
        (ternaryPageColorSignature query selected clause).card ≤
          Fintype.card (TernaryPage query) :=
      Finset.card_le_univ _
    have hsignatureCard :
        (ternaryPageColorSignature query selected clause).card =
          Fintype.card (TernaryPage query) := by
      rw [hpageCard] at hsignatureLe ⊢
      omega
    have huniv :
        ternaryPageColorSignature query selected clause =
          Finset.univ :=
      Finset.eq_univ_of_card _ hsignatureCard
    apply hmissing
    apply Finset.mem_image.mpr
    refine ⟨clause, Finset.mem_univ _, ?_⟩
    funext player
    have hmem :
        player ∈
          ternaryPageColorSignature query selected clause := by
      rw [huniv]
      simp
    exact (Finset.mem_filter.mp hmem).2

/-- Balanced occurrence-signature system on the ternary pages. -/
def ternaryPageColorSignatureSystem
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (selected : TernaryPage query → FourByThreeQuestion)
    (hselection :
      Fintype.card (TernaryPage query) ≤ 2 ∨
        (Fintype.card (TernaryPage query) = 3 ∧
          selected ∉
            Finset.univ.image (ternaryPageProjection query))) :
    ColorSignatureSystem
      (TernaryPage query)
      (PositiveOccurrence y) (NegativeOccurrence y) where
  positiveSignature occurrence :=
    ternaryPageColorSignature query selected occurrence.1
  negativeSignature occurrence :=
    ternaryPageColorSignature query selected occurrence.1
  positive_card_le_two occurrence :=
    ternaryPageColorSignature_card_le_two
      query selected hselection occurrence.1
  negative_card_le_two occurrence :=
    ternaryPageColorSignature_card_le_two
      query selected hselection occurrence.1
  balanced := by
    intro player
    simpa [ternaryPageColorSignature] using
      occurrenceQuestion_filter_card_eq
        query y hy player.1 (selected player)

/--
A linear-forest selected-block certificate on precisely the ternary pages;
all remaining pages have at most two used labels.
-/
structure TernaryPageLinearForestCertificate
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ) where
  selectedQuestion :
    TernaryPage query → FourByThreeQuestion
  Match :
    TernaryPage query →
      PositiveOccurrence y → NegativeOccurrence y → Prop
  match_mem :
    ∀ {player positive negative},
      Match player positive negative →
        query positive.1 player.1 = selectedQuestion player ∧
          query negative.1 player.1 = selectedQuestion player
  positive_unique :
    ∀ player positive,
      query positive.1 player.1 = selectedQuestion player →
        ∃! negative, Match player positive negative
  negative_unique :
    ∀ player negative,
      query negative.1 player.1 = selectedQuestion player →
        ∃! positive, Match player positive negative
  linear_forest :
    (selectedBlockSimpleGraph Match).IsAcyclic ∧
      ∀ vertex,
        ((selectedBlockSimpleGraph Match).neighborSet vertex).ncard ≤ 2
  nonternary_card_le_two :
    ∀ player : FourByThreePlayer,
      player ∉ ternaryPlayers query →
        usedQuestionsCard query player ≤ 2

/--
The at-most-three-ternary-page hypothesis produces the selected-block
linear forest required by the selected-block lift construction.  The bound `26` is only the
pigeonhole threshold for an omitted ternary triple.
-/
theorem hasTernaryPageLinearForestCertificate_of_card_le_three
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (hpages : (ternaryPlayers query).card ≤ 3)
    (hcard : Fintype.card E ≤ 26) :
    Nonempty (TernaryPageLinearForestCertificate query y) := by
  classical
  obtain ⟨selected, hselection⟩ :=
    exists_ternaryPageSelection_with_small_or_missing
      query hpages hcard
  let system :=
    ternaryPageColorSignatureSystem
      query y hy selected hselection
  have hcolorCard :
      Fintype.card (TernaryPage query) ≤ 3 := by
    rw [Fintype.card_coe]
    exact hpages
  obtain ⟨matching, hforest⟩ :=
    threeColor_colorwiseMatching_linearForest system hcolorCard
  refine ⟨{
    selectedQuestion := selected
    Match := matching.Match
    match_mem := ?_
    positive_unique := ?_
    negative_unique := ?_
    linear_forest := ?_
    nonternary_card_le_two := ?_
  }⟩
  · intro player positive negative hmatch
    simpa [system, ternaryPageColorSignatureSystem,
      ternaryPageColorSignature] using matching.match_mem hmatch
  · intro player positive hpositive
    apply matching.positive_unique
    simpa [system, ternaryPageColorSignatureSystem,
      ternaryPageColorSignature] using hpositive
  · intro player negative hnegative
    apply matching.negative_unique
    simpa [system, ternaryPageColorSignatureSystem,
      ternaryPageColorSignature] using hnegative
  · constructor
    · have hgraph :
          selectedBlockSimpleGraph matching.Match =
            matching.simpleGraph :=
        selectedBlockSimpleGraph_comp_surjective
          matching id Function.surjective_id
      rw [hgraph]
      exact hforest.1
    · intro vertex
      have hgraph :
          selectedBlockSimpleGraph matching.Match =
            matching.simpleGraph :=
        selectedBlockSimpleGraph_comp_surjective
          matching id Function.surjective_id
      rw [hgraph, ← Set.fintypeCard_eq_ncard,
        matching.simpleGraph.card_neighborSet_eq_degree]
      exact hforest.2 vertex
  · intro player hnotTernary
    have hle := usedQuestionsCard_le_three query player
    have hne : usedQuestionsCard query player ≠ 3 := by
      intro heq
      exact hnotTernary <| by
        simp [ternaryPlayers, heq]
    omega

end

end XORGame
end QIT

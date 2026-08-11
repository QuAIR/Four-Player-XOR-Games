/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.BoundaryFibers
public import XORGameFormalization.Hamming

/-!
# Hard-center Hamming geometry

This module isolates the geometric separation argument used in the
safe-center analysis.  It proves
that even support distances rule out centers at distance one.  Centers at
distance two force two complete third-question fibers to coincide, and a
support of size at most ten makes that shared block omit a cell in its
projection to the remaining two pages.

The final separation theorem keeps the matching-theoretic step explicit as
an abstract escape hypothesis.  No matching or forest conclusion is asserted
here.
-/

@[expose] public section

namespace QIT
namespace XORGame

open scoped BigOperators

universe uE

noncomputable section

theorem exists_questionValue_ne_two
    (x y : FourByThreeQuestion) :
    ∃ z : FourByThreeQuestion, z ≠ x ∧ z ≠ y := by
  have hpair :
      ({x, y} : Finset FourByThreeQuestion).card ≤ 2 :=
    Finset.card_le_two
  have huniv :
      (Finset.univ : Finset FourByThreeQuestion).card = 3 :=
    Fintype.card_fin 3
  have hlt :
      ({x, y} : Finset FourByThreeQuestion).card <
        (Finset.univ : Finset FourByThreeQuestion).card := by
    omega
  obtain ⟨z, _hzUniv, hzPair⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzPair
  exact ⟨z, hzPair.1, hzPair.2⟩

/-- A deterministic question value different from two specified values. -/
noncomputable def thirdQuestionValue
    (x y : FourByThreeQuestion) : FourByThreeQuestion :=
  Classical.choose (exists_questionValue_ne_two x y)

theorem thirdQuestionValue_ne_left
    (x y : FourByThreeQuestion) :
    thirdQuestionValue x y ≠ x :=
  (Classical.choose_spec (exists_questionValue_ne_two x y)).1

theorem thirdQuestionValue_ne_right
    (x y : FourByThreeQuestion) :
    thirdQuestionValue x y ≠ y :=
  (Classical.choose_spec (exists_questionValue_ne_two x y)).2

private theorem eq_thirdQuestionValue_of_ne
    (x y z : FourByThreeQuestion)
    (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y) :
    z = thirdQuestionValue x y := by
  by_contra hzthird
  let third := thirdQuestionValue x y
  let fourValues : Finset FourByThreeQuestion :=
    {x, y, z, third}
  have hfourValuesCard : fourValues.card = 4 := by
    have hzNot : z ∉ ({third} : Finset FourByThreeQuestion) := by
      simpa [third] using hzthird
    have hyNot : y ∉ ({z, third} : Finset FourByThreeQuestion) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hzy.symm,
        (thirdQuestionValue_ne_right x y).symm⟩
    have hxNot : x ∉ ({y, z, third} : Finset FourByThreeQuestion) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hxy, hzx.symm,
        (thirdQuestionValue_ne_left x y).symm⟩
    rw [show fourValues = insert x {y, z, third} by rfl,
      Finset.card_insert_of_notMem hxNot,
      Finset.card_insert_of_notMem hyNot,
      Finset.card_insert_of_notMem hzNot]
    simp
  have hcardLe :
      fourValues.card ≤
        (Finset.univ : Finset FourByThreeQuestion).card :=
    Finset.card_le_card (Finset.subset_univ fourValues)
  rw [hfourValuesCard] at hcardLe
  norm_num at hcardLe

/-- Every support clause has even Hamming distance from `center`. -/
def EvenSupportDistances
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (center : FourByThreeClause) : Prop :=
  ∀ clause : E, Even (hammingDistance center (query clause))

/-- Coordinates at which two clauses differ. -/
def differingPlayers
    (x y : FourByThreeClause) : Finset FourByThreePlayer :=
  Finset.univ.filter fun player => x player ≠ y player

@[simp]
theorem differingPlayers_card
    (x y : FourByThreeClause) :
    (differingPlayers x y).card = hammingDistance x y := rfl

@[simp]
theorem mem_differingPlayers
    (x y : FourByThreeClause) (player : FourByThreePlayer) :
    player ∈ differingPlayers x y ↔ x player ≠ y player := by
  simp [differingPlayers]

private def mismatchCountAwayFrom
    (player : FourByThreePlayer)
    (x y : FourByThreeClause) : Nat :=
  ((Finset.univ.erase player).filter fun coordinate =>
    x coordinate ≠ y coordinate).card

private theorem hammingDistance_decompose_one
    (x y : FourByThreeClause) (player : FourByThreePlayer) :
    hammingDistance x y =
      (if x player ≠ y player then 1 else 0) +
        mismatchCountAwayFrom player x y := by
  let differs : FourByThreePlayer → Prop :=
    fun coordinate => x coordinate ≠ y coordinate
  have hfull :
      (∑ coordinate : FourByThreePlayer,
          if differs coordinate then 1 else 0) =
        hammingDistance x y := by
    exact Finset.sum_boole differs Finset.univ
  have haway :
      (∑ coordinate ∈
          (Finset.univ : Finset FourByThreePlayer).erase player,
          if differs coordinate then 1 else 0) =
        mismatchCountAwayFrom player x y := by
    exact Finset.sum_boole differs
      ((Finset.univ : Finset FourByThreePlayer).erase player)
  rw [← hfull, ← haway]
  exact (Finset.add_sum_erase Finset.univ
    (fun coordinate => if differs coordinate then 1 else 0)
    (Finset.mem_univ player)).symm

private theorem mismatchCountAwayFrom_eq_of_eq_off
    (x y clause : FourByThreeClause)
    (player : FourByThreePlayer)
    (hoff : ∀ coordinate, coordinate ≠ player →
      x coordinate = y coordinate) :
    mismatchCountAwayFrom player x clause =
      mismatchCountAwayFrom player y clause := by
  unfold mismatchCountAwayFrom
  congr 1
  ext coordinate
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨hne, hdiff⟩
    exact ⟨hne, by simpa only [hoff coordinate hne] using hdiff⟩
  · rintro ⟨hne, hdiff⟩
    exact ⟨hne, by simpa only [hoff coordinate hne] using hdiff⟩

private theorem mismatchIndicator_eq_of_even_support_distances
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (x y : FourByThreeClause)
    (player : FourByThreePlayer)
    (hoff : ∀ coordinate, coordinate ≠ player →
      x coordinate = y coordinate)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y)
    (clause : E) :
    (if x player ≠ query clause player then 1 else 0) =
      if y player ≠ query clause player then 1 else 0 := by
  have hxDecompose :=
    hammingDistance_decompose_one x (query clause) player
  have hyDecompose :=
    hammingDistance_decompose_one y (query clause) player
  have haway :=
    mismatchCountAwayFrom_eq_of_eq_off
      x y (query clause) player hoff
  obtain ⟨xhalf, hxParity⟩ := hxEven clause
  obtain ⟨yhalf, hyParity⟩ := hyEven clause
  by_cases hxMismatch : x player ≠ query clause player <;>
    by_cases hyMismatch : y player ≠ query clause player
  · simp [hxMismatch, hyMismatch]
  · simp only [if_pos hxMismatch, if_neg hyMismatch]
    simp [hxMismatch, hyMismatch] at hxDecompose hyDecompose
    omega
  · simp only [if_neg hxMismatch, if_pos hyMismatch]
    simp [hxMismatch, hyMismatch] at hxDecompose hyDecompose
    omega
  · simp [hxMismatch, hyMismatch]

private theorem distance_one_coordinates
    (x y : FourByThreeClause)
    (hdistance : hammingDistance x y = 1) :
    ∃ player : FourByThreePlayer,
      x player ≠ y player ∧
        ∀ coordinate, coordinate ≠ player →
          x coordinate = y coordinate := by
  have hcard : (differingPlayers x y).card = 1 := by
    simpa using hdistance
  obtain ⟨player, hplayers⟩ := Finset.card_eq_one.mp hcard
  refine ⟨player, ?_, ?_⟩
  · have : player ∈ differingPlayers x y := by
      rw [hplayers]
      simp
    exact (mem_differingPlayers x y player).mp this
  · intro coordinate hne
    by_contra hdiffer
    have hmem : coordinate ∈ differingPlayers x y :=
      (mem_differingPlayers x y coordinate).mpr hdiffer
    rw [hplayers] at hmem
    simp only [Finset.mem_singleton] at hmem
    exact hne hmem

/--
On four ternary pages, two centers having even distances to every support
clause cannot be at Hamming distance one.
-/
theorem evenSupportDistances_distance_one_impossible
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hternary :
      ∀ player : FourByThreePlayer,
        usedQuestionsCard query player = 3)
    (x y : FourByThreeClause)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y) :
    hammingDistance x y ≠ 1 := by
  intro hdistance
  obtain ⟨player, hdiffer, hoff⟩ :=
    distance_one_coordinates x y hdistance
  let third :=
    thirdQuestionValue (x player) (y player)
  have hallThird :
      ∀ clause : E, query clause player = third := by
    intro clause
    have hindicator :=
      mismatchIndicator_eq_of_even_support_distances
        query x y player hoff hxEven hyEven clause
    have hneLeft : query clause player ≠ x player := by
      intro hleft
      rw [hleft] at hindicator
      simp at hindicator
      exact hdiffer hindicator.symm
    have hneRight : query clause player ≠ y player := by
      intro hright
      rw [hright] at hindicator
      simp at hindicator
      exact hdiffer hindicator
    exact eq_thirdQuestionValue_of_ne
      (x player) (y player) (query clause player)
      hdiffer hneLeft hneRight
  have husedSubset :
      usedQuestions query player ⊆ {third} := by
    intro question hquestion
    obtain ⟨clause, hclause⟩ :=
      (mem_usedQuestions query player question).mp hquestion
    simp only [Finset.mem_singleton]
    exact hclause.symm.trans (hallThird clause)
  have husedCard :=
    Finset.card_le_card husedSubset
  have hthree := hternary player
  simp only [usedQuestionsCard] at hthree
  simp at husedCard
  omega

private def mismatchCountAwayFromTwo
    (first second : FourByThreePlayer)
    (x y : FourByThreeClause) : Nat :=
  ((((Finset.univ : Finset FourByThreePlayer).erase first).erase second).filter
    fun coordinate => x coordinate ≠ y coordinate).card

private theorem hammingDistance_decompose_two
    (x y : FourByThreeClause)
    (first second : FourByThreePlayer)
    (hne : first ≠ second) :
    hammingDistance x y =
      (if x first ≠ y first then 1 else 0) +
        (if x second ≠ y second then 1 else 0) +
          mismatchCountAwayFromTwo first second x y := by
  let differs : FourByThreePlayer → Prop :=
    fun coordinate => x coordinate ≠ y coordinate
  let awayFirst :=
    (Finset.univ : Finset FourByThreePlayer).erase first
  have hsecondMem : second ∈ awayFirst := by
    simp [awayFirst, hne.symm]
  have hfull :
      (∑ coordinate : FourByThreePlayer,
          if differs coordinate then 1 else 0) =
        hammingDistance x y := by
    exact Finset.sum_boole differs Finset.univ
  have haway :
      (∑ coordinate ∈ awayFirst.erase second,
          if differs coordinate then 1 else 0) =
        mismatchCountAwayFromTwo first second x y := by
    exact Finset.sum_boole differs (awayFirst.erase second)
  calc
    hammingDistance x y =
        ∑ coordinate : FourByThreePlayer,
          if differs coordinate then 1 else 0 := hfull.symm
    _ =
        (if differs first then 1 else 0) +
          ∑ coordinate ∈ awayFirst,
            if differs coordinate then 1 else 0 := by
      exact (Finset.add_sum_erase Finset.univ
        (fun coordinate => if differs coordinate then 1 else 0)
        (Finset.mem_univ first)).symm
    _ =
        (if differs first then 1 else 0) +
          ((if differs second then 1 else 0) +
            ∑ coordinate ∈ awayFirst.erase second,
              if differs coordinate then 1 else 0) := by
      rw [Finset.add_sum_erase awayFirst
        (fun coordinate => if differs coordinate then 1 else 0)
        hsecondMem]
    _ =
        (if x first ≠ y first then 1 else 0) +
          (if x second ≠ y second then 1 else 0) +
            mismatchCountAwayFromTwo first second x y := by
      rw [haway]
      simp only [differs]
      omega

private theorem mismatchCountAwayFromTwo_eq_of_eq_off
    (x y clause : FourByThreeClause)
    (first second : FourByThreePlayer)
    (hoff :
      ∀ coordinate, coordinate ≠ first → coordinate ≠ second →
        x coordinate = y coordinate) :
    mismatchCountAwayFromTwo first second x clause =
      mismatchCountAwayFromTwo first second y clause := by
  unfold mismatchCountAwayFromTwo
  congr 1
  ext coordinate
  simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨⟨hneSecond, hneFirst⟩, hdiff⟩
    exact ⟨⟨hneSecond, hneFirst⟩,
      by simpa only [hoff coordinate hneFirst hneSecond] using hdiff⟩
  · rintro ⟨⟨hneSecond, hneFirst⟩, hdiff⟩
    exact ⟨⟨hneSecond, hneFirst⟩,
      by simpa only [hoff coordinate hneFirst hneSecond] using hdiff⟩

private theorem eq_left_or_eq_right_of_ne_thirdQuestionValue
    (x y z : FourByThreeQuestion)
    (hxy : x ≠ y)
    (hzthird : z ≠ thirdQuestionValue x y) :
    z = x ∨ z = y := by
  by_cases hzx : z = x
  · exact Or.inl hzx
  by_cases hzy : z = y
  · exact Or.inr hzy
  exact False.elim (hzthird
    (eq_thirdQuestionValue_of_ne x y z hxy hzx hzy))

private theorem thirdQuestionCoordinates_iff_of_even_support_distances
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (x y : FourByThreeClause)
    (first second : FourByThreePlayer)
    (hne : first ≠ second)
    (hdifferFirst : x first ≠ y first)
    (hdifferSecond : x second ≠ y second)
    (hoff :
      ∀ coordinate, coordinate ≠ first → coordinate ≠ second →
        x coordinate = y coordinate)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y)
    (clause : E) :
    query clause first =
        thirdQuestionValue (x first) (y first) ↔
      query clause second =
        thirdQuestionValue (x second) (y second) := by
  have hxDecompose :=
    hammingDistance_decompose_two x (query clause) first second hne
  have hyDecompose :=
    hammingDistance_decompose_two y (query clause) first second hne
  have haway :=
    mismatchCountAwayFromTwo_eq_of_eq_off
      x y (query clause) first second hoff
  obtain ⟨xhalf, hxParity⟩ := hxEven clause
  obtain ⟨yhalf, hyParity⟩ := hyEven clause
  rw [hxDecompose] at hxParity
  rw [hyDecompose, ← haway] at hyParity
  constructor
  · intro hfirst
    by_contra hsecond
    have hsecondCases :=
      eq_left_or_eq_right_of_ne_thirdQuestionValue
        (x second) (y second) (query clause second)
        hdifferSecond hsecond
    rcases hsecondCases with hsecondLeft | hsecondRight
    · have hxFirst :
          x first ≠ thirdQuestionValue (x first) (y first) :=
        (thirdQuestionValue_ne_left (x first) (y first)).symm
      have hyFirst :
          y first ≠ thirdQuestionValue (x first) (y first) :=
        (thirdQuestionValue_ne_right (x first) (y first)).symm
      have hySecond : y second ≠ x second := hdifferSecond.symm
      simp [hfirst, hxFirst, hyFirst, hsecondLeft, hySecond] at hxParity hyParity
      omega
    · have hxFirst :
          x first ≠ thirdQuestionValue (x first) (y first) :=
        (thirdQuestionValue_ne_left (x first) (y first)).symm
      have hyFirst :
          y first ≠ thirdQuestionValue (x first) (y first) :=
        (thirdQuestionValue_ne_right (x first) (y first)).symm
      simp [hfirst, hxFirst, hyFirst, hsecondRight,
        hdifferSecond] at hxParity hyParity
      omega
  · intro hsecond
    by_contra hfirst
    have hfirstCases :=
      eq_left_or_eq_right_of_ne_thirdQuestionValue
        (x first) (y first) (query clause first)
        hdifferFirst hfirst
    rcases hfirstCases with hfirstLeft | hfirstRight
    · have hxSecond :
          x second ≠ thirdQuestionValue (x second) (y second) :=
        (thirdQuestionValue_ne_left (x second) (y second)).symm
      have hySecond :
          y second ≠ thirdQuestionValue (x second) (y second) :=
        (thirdQuestionValue_ne_right (x second) (y second)).symm
      have hyFirst : y first ≠ x first := hdifferFirst.symm
      simp [hfirstLeft, hyFirst, hsecond, hxSecond, hySecond] at hxParity hyParity
      omega
    · have hxSecond :
          x second ≠ thirdQuestionValue (x second) (y second) :=
        (thirdQuestionValue_ne_left (x second) (y second)).symm
      have hySecond :
          y second ≠ thirdQuestionValue (x second) (y second) :=
        (thirdQuestionValue_ne_right (x second) (y second)).symm
      simp [hfirstRight, hdifferFirst, hsecond, hxSecond, hySecond] at hxParity hyParity
      omega

private theorem distance_two_coordinates
    (x y : FourByThreeClause)
    (hdistance : hammingDistance x y = 2) :
    ∃ first second : FourByThreePlayer,
      first ≠ second ∧
        x first ≠ y first ∧
        x second ≠ y second ∧
        ∀ coordinate, coordinate ≠ first → coordinate ≠ second →
          x coordinate = y coordinate := by
  have hcard : (differingPlayers x y).card = 2 := by
    simpa using hdistance
  obtain ⟨first, second, hne, hplayers⟩ :=
    Finset.card_eq_two.mp hcard
  refine ⟨first, second, hne, ?_, ?_, ?_⟩
  · apply (mem_differingPlayers x y first).mp
    rw [hplayers]
    simp
  · apply (mem_differingPlayers x y second).mp
    rw [hplayers]
    simp
  · intro coordinate hneFirst hneSecond
    by_contra hdiffer
    have hmem : coordinate ∈ differingPlayers x y :=
      (mem_differingPlayers x y coordinate).mpr hdiffer
    rw [hplayers] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    exact hmem.elim hneFirst hneSecond

/--
If two even-distance centers differ in exactly two coordinates, the complete
fibers of their respective third question values on those coordinates agree.
-/
theorem distanceTwo_evenSupportDistances_sharedThirdQuestionFibers
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (x y : FourByThreeClause)
    (hdistance : hammingDistance x y = 2)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y) :
    ∃ first second : FourByThreePlayer,
      first ≠ second ∧
        x first ≠ y first ∧
        x second ≠ y second ∧
        (∀ coordinate, coordinate ≠ first → coordinate ≠ second →
          x coordinate = y coordinate) ∧
        questionFiber query first
            (thirdQuestionValue (x first) (y first)) =
          questionFiber query second
            (thirdQuestionValue (x second) (y second)) := by
  obtain ⟨first, second, hne, hdifferFirst, hdifferSecond, hoff⟩ :=
    distance_two_coordinates x y hdistance
  refine ⟨first, second, hne, hdifferFirst, hdifferSecond, hoff, ?_⟩
  ext clause
  simp only [mem_questionFiber]
  exact thirdQuestionCoordinates_iff_of_even_support_distances
    query x y first second hne hdifferFirst hdifferSecond hoff
      hxEven hyEven clause

/-- The two player pages other than `first` and `second`. -/
abbrev RemainingPlayers
    (first second : FourByThreePlayer) :=
  {player : FourByThreePlayer //
    player ≠ first ∧ player ≠ second}

@[simp]
theorem remainingPlayers_card
    (first second : FourByThreePlayer)
    (hne : first ≠ second) :
    Fintype.card (RemainingPlayers first second) = 2 := by
  classical
  rw [Fintype.card_subtype]
  have hremaining :
      (Finset.univ.filter fun player : FourByThreePlayer =>
          player ≠ first ∧ player ≠ second) =
        (Finset.univ : Finset FourByThreePlayer) \ {first, second} := by
    ext player
    simp
  rw [hremaining, Finset.card_sdiff]
  simp [hne]

/-- Restriction of a clause to the two pages complementary to a player pair. -/
def remainingQuestionProjection
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (first second : FourByThreePlayer)
    (clause : E) :
    RemainingPlayers first second → FourByThreeQuestion :=
  fun player => query clause player.1

/--
On a ternary page in a support of size at most ten, every complete question
fiber has at most eight clauses.
-/
theorem ternary_questionFiber_card_le_eight
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E ≤ 10)
    (player : FourByThreePlayer)
    (hternary : usedQuestionsCard query player = 3)
    (question : FourByThreeQuestion) :
    (questionFiber query player question).card ≤ 8 := by
  let otherQuestions :=
    {other : FourByThreeQuestion // other ≠ question}
  have hotherCard : Fintype.card otherQuestions = 2 := by
    simp [otherQuestions]
  have hotherLower :
      2 ≤
        ∑ other : otherQuestions,
          (questionFiber query player other.1).card := by
    calc
      2 = ∑ _other : otherQuestions, 1 := by
        simp [hotherCard]
      _ ≤
          ∑ other : otherQuestions,
            (questionFiber query player other.1).card := by
        apply Finset.sum_le_sum
        intro other _
        exact questionFiber_card_pos_of_mem_usedQuestions
          query player other.1
            (mem_usedQuestions_of_card_three
              query player hternary other.1)
  have hdecompose :=
    Fintype.sum_eq_add_sum_subtype_ne
      (fun other : FourByThreeQuestion =>
        (questionFiber query player other).card)
      question
  have hsum := sum_questionFiber_card query player
  rw [hsum] at hdecompose
  change
    Fintype.card E =
      (questionFiber query player question).card +
        ∑ other : otherQuestions,
          (questionFiber query player other.1).card at hdecompose
  omega

/--
A complete question fiber of size at most eight omits a cell in its
projection to the two remaining ternary pages.
-/
theorem questionFiber_remainingProjection_missingCell
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E ≤ 10)
    (first second : FourByThreePlayer)
    (hne : first ≠ second)
    (hfirstTernary : usedQuestionsCard query first = 3)
    (question : FourByThreeQuestion) :
    ∃ cell : RemainingPlayers first second → FourByThreeQuestion,
      cell ∉
        (questionFiber query first question).image
          (remainingQuestionProjection query first second) := by
  classical
  let projected :=
    (questionFiber query first question).image
      (remainingQuestionProjection query first second)
  have hfiberCard :
      (questionFiber query first question).card ≤ 8 :=
    ternary_questionFiber_card_le_eight
      query hcard first hfirstTernary question
  have hprojectedCard : projected.card ≤ 8 :=
    (Finset.card_image_le.trans hfiberCard)
  have hcellCard :
      Fintype.card
        (RemainingPlayers first second → FourByThreeQuestion) = 9 := by
    rw [Fintype.card_fun, remainingPlayers_card first second hne]
    norm_num
  have hlt :
      projected.card <
        (Finset.univ :
          Finset (RemainingPlayers first second →
            FourByThreeQuestion)).card := by
    rw [Finset.card_univ, hcellCard]
    omega
  obtain ⟨cell, _hcellUniv, hcellMissing⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨cell, hcellMissing⟩

/--
The exact distance-two geometric obstruction: two third-question blocks
coincide and their projection to the complementary pages misses a cell.
-/
def HasSharedThirdQuestionBlockMissingCell
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (x y : FourByThreeClause) : Prop :=
  ∃ first second : FourByThreePlayer,
    first ≠ second ∧
      x first ≠ y first ∧
      x second ≠ y second ∧
      (∀ coordinate, coordinate ≠ first → coordinate ≠ second →
        x coordinate = y coordinate) ∧
      questionFiber query first
          (thirdQuestionValue (x first) (y first)) =
        questionFiber query second
          (thirdQuestionValue (x second) (y second)) ∧
      (questionFiber query first
        (thirdQuestionValue (x first) (y first))).Nonempty ∧
      (questionFiber query first
        (thirdQuestionValue (x first) (y first))).card ≤ 8 ∧
      ∃ cell : RemainingPlayers first second → FourByThreeQuestion,
          cell ∉
            (questionFiber query first
              (thirdQuestionValue (x first) (y first))).image
                (remainingQuestionProjection query first second)

/--
Distance two, even cross-distances, four ternary pages, and support size at
most ten produce the complete shared-block/missing-cell obstruction.
-/
theorem distanceTwo_evenSupportDistances_sharedBlock_missingCell
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E ≤ 10)
    (hternary :
      ∀ player : FourByThreePlayer,
        usedQuestionsCard query player = 3)
    (x y : FourByThreeClause)
    (hdistance : hammingDistance x y = 2)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y) :
    HasSharedThirdQuestionBlockMissingCell query x y := by
  obtain ⟨first, second, hne, hdifferFirst, hdifferSecond,
      hoff, hshared⟩ :=
    distanceTwo_evenSupportDistances_sharedThirdQuestionFibers
      query x y hdistance hxEven hyEven
  obtain ⟨cell, hcell⟩ :=
    questionFiber_remainingProjection_missingCell
      query hcard first second hne (hternary first)
        (thirdQuestionValue (x first) (y first))
  have hblockPositive :
      0 <
        (questionFiber query first
          (thirdQuestionValue (x first) (y first))).card :=
    questionFiber_card_pos_of_mem_usedQuestions
      query first (thirdQuestionValue (x first) (y first))
        (mem_usedQuestions_of_card_three
          query first (hternary first)
            (thirdQuestionValue (x first) (y first)))
  have hblockCard :
      (questionFiber query first
        (thirdQuestionValue (x first) (y first))).card ≤ 8 :=
    ternary_questionFiber_card_le_eight query hcard first
      (hternary first) (thirdQuestionValue (x first) (y first))
  exact ⟨first, second, hne, hdifferFirst, hdifferSecond,
    hoff, hshared, Finset.card_pos.mp hblockPositive,
      hblockCard, cell, hcell⟩

/--
Abstract separation endpoint for the safe-center argument.

Instantiate `Escape` with liftability (or with failure of hardness).  The
hypothesis `hescape` states that the precise shared-third-block/missing-cell
witness implies `Escape`.
-/
theorem evenSupportDistances_separated_of_sharedBlockMissingCell_escape
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E ≤ 10)
    (hternary :
      ∀ player : FourByThreePlayer,
        usedQuestionsCard query player = 3)
    (Escape : Prop)
    (hescape :
      ∀ x y : FourByThreeClause,
        HasSharedThirdQuestionBlockMissingCell query x y →
          Escape)
    (hnoEscape : ¬Escape)
    (x y : FourByThreeClause)
    (hne : x ≠ y)
    (hxEven : EvenSupportDistances query x)
    (hyEven : EvenSupportDistances query y) :
    3 ≤ hammingDistance x y := by
  have hpositive :
      1 ≤ hammingDistance x y := by
    exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
      hne ((hammingDistance_eq_zero_iff x y).mp hzero)
  by_contra hnotThree
  have hcases :
      hammingDistance x y = 1 ∨
        hammingDistance x y = 2 := by
    omega
  rcases hcases with hone | htwo
  · exact evenSupportDistances_distance_one_impossible
      query hternary x y hxEven hyEven hone
  · exact hnoEscape
      (hescape x y
        (distanceTwo_evenSupportDistances_sharedBlock_missingCell
          query hcard hternary x y htwo hxEven hyEven))

end

end XORGame
end QIT

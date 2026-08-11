/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Hamming
public import XORGameFormalization.TernaryCode
public import XORGameFormalization.Circuit
public import Mathlib.Data.Nat.Choose.Cast

/-!
# The structural ten-ball-cover obstruction

This module isolates the double-counting core of the ten-clause boundary.
Ten distinct radius-one Hamming balls covering the 81-word ternary clause
space meet every perfect-code coset with multiplicity profile
`(2, 1, ..., 1)`.  Consequently the total mass of pairwise ball
intersections is nine, and hence `3 n₁ + 2 n₂ = 9`.

The arguments below are uniform finite-set identities.  Closed computations
about the fixed ternary code and Hamming balls live in `TernaryCode` and
`Hamming`; no circuit-support census is used here.
-/

@[expose] public section

namespace QIT
namespace XORGame

/-- The number of selected radius-one balls which contain `point`. -/
def ballCoverMultiplicity
    (centers : Finset FourByThreeClause) (point : FourByThreeClause) : Nat :=
  (centers.filter fun center => point ∈ radiusOneBall center).card

/-- A finite set of centers whose radius-one balls cover the clause space. -/
def RadiusOneBallCover (centers : Finset FourByThreeClause) : Prop :=
  ∀ point : FourByThreeClause, 1 ≤ ballCoverMultiplicity centers point

/--
Each selected ball contributes exactly once to the total multiplicity on a
fixed ternary perfect-code coset.
-/
theorem sum_ballCoverMultiplicity_ternaryCoset
    (centers : Finset FourByThreeClause) (syndrome : TernarySyndrome) :
    ∑ point ∈ ternaryCoset syndrome, ballCoverMultiplicity centers point =
      centers.card := by
  classical
  simp only [ballCoverMultiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ center ∈ centers,
        ∑ point ∈ ternaryCoset syndrome,
          if point ∈ radiusOneBall center then 1 else 0) =
        ∑ center ∈ centers,
          (ternaryCoset syndrome ∩ radiusOneBall center).card := by
      apply Finset.sum_congr rfl
      intro center _
      have hinter :
          (ternaryCoset syndrome).filter
              (fun point => point ∈ radiusOneBall center) =
            ternaryCoset syndrome ∩ radiusOneBall center := by
        ext point
        simp
      rw [← hinter, Finset.card_filter]
    _ = centers.card := by
      simp [Finset.inter_comm, radiusOneBall_inter_ternaryCoset_card]

/--
Abstract arithmetic behind the coset profile: nine positive natural
multiplicities with total ten consist of one `2` and eight `1`s.
-/
private theorem existsUnique_double_of_card_nine_sum_ten
    {α : Type*} [DecidableEq α] (points : Finset α) (multiplicity : α → Nat)
    (hcard : points.card = 9)
    (hsum : ∑ point ∈ points, multiplicity point = 10)
    (hpositive : ∀ point ∈ points, 1 ≤ multiplicity point) :
    ∃! doublePoint : α,
      doublePoint ∈ points ∧
        multiplicity doublePoint = 2 ∧
        ∀ point ∈ points, point ≠ doublePoint → multiplicity point = 1 := by
  have hexcess :
      ∑ point ∈ points, (multiplicity point - 1) = 1 := by
    have hbalance :
        (∑ point ∈ points, (multiplicity point - 1)) + points.card =
          ∑ point ∈ points, multiplicity point := by
      calc
        (∑ point ∈ points, (multiplicity point - 1)) + points.card =
            (∑ point ∈ points, (multiplicity point - 1)) +
              ∑ _point ∈ points, 1 := by simp
        _ = ∑ point ∈ points, ((multiplicity point - 1) + 1) := by
          rw [Finset.sum_add_distrib]
        _ = ∑ point ∈ points, multiplicity point := by
          apply Finset.sum_congr rfl
          intro point hpoint
          exact Nat.sub_add_cancel (hpositive point hpoint)
    omega
  have hexcess_ne :
      ∑ point ∈ points, (multiplicity point - 1) ≠ 0 := by
    omega
  obtain ⟨doublePoint, hdouble_mem, hdouble_nonzero⟩ :=
    Finset.exists_ne_zero_of_sum_ne_zero hexcess_ne
  have hdouble_le :
      multiplicity doublePoint - 1 ≤
        ∑ point ∈ points, (multiplicity point - 1) :=
    Finset.single_le_sum
      (f := fun point => multiplicity point - 1)
      (fun _ _ => Nat.zero_le _) hdouble_mem
  have hdouble_excess : multiplicity doublePoint - 1 = 1 := by
    omega
  have hdouble : multiplicity doublePoint = 2 := by
    have := hpositive doublePoint hdouble_mem
    omega
  have hrest :
      ∑ point ∈ points.erase doublePoint, (multiplicity point - 1) = 0 := by
    have herase :=
      Finset.sum_erase_add points
        (fun point => multiplicity point - 1) hdouble_mem
    change
      (∑ point ∈ points.erase doublePoint, (multiplicity point - 1)) +
          (multiplicity doublePoint - 1) =
        ∑ point ∈ points, (multiplicity point - 1) at herase
    rw [hdouble_excess, hexcess] at herase
    omega
  have hsingle :
      ∀ point ∈ points, point ≠ doublePoint → multiplicity point = 1 := by
    intro point hpoint_mem hpoint_ne
    have hpoint_erase : point ∈ points.erase doublePoint := by
      simp [hpoint_mem, hpoint_ne]
    have hzero :
        multiplicity point - 1 = 0 :=
      (Finset.sum_eq_zero_iff.mp hrest) point hpoint_erase
    have := hpositive point hpoint_mem
    omega
  refine ⟨doublePoint, ⟨hdouble_mem, hdouble, hsingle⟩, ?_⟩
  intro other hother
  by_contra hne
  have hone := hsingle other hother.1 hne
  omega

/--
On each perfect-code coset, a ten-ball cover has exactly one
double-covered point and all other points are covered exactly once.
-/
theorem tenBallCover_coset_multiplicity_profile
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers)
    (syndrome : TernarySyndrome) :
    ∃! doublePoint : FourByThreeClause,
      doublePoint ∈ ternaryCoset syndrome ∧
        ballCoverMultiplicity centers doublePoint = 2 ∧
        ∀ point ∈ ternaryCoset syndrome,
          point ≠ doublePoint →
            ballCoverMultiplicity centers point = 1 := by
  apply existsUnique_double_of_card_nine_sum_ten
  · exact ternaryCoset_card syndrome
  · simpa [hcard] using
      sum_ballCoverMultiplicity_ternaryCoset centers syndrome
  · intro point _
    exact hcover point

/-- The unordered two-element subsets of a set of ball centers. -/
def centerPairs (centers : Finset FourByThreeClause) :
    Finset (Finset FourByThreeClause) :=
  centers.powersetCard 2

/-- The points common to all balls whose centers lie in `pair`. -/
def commonBallPoints (pair : Finset FourByThreeClause) :
    Finset FourByThreeClause :=
  Finset.univ.filter fun point =>
    ∀ center ∈ pair, point ∈ radiusOneBall center

/-- Total pairwise intersection mass of the selected radius-one balls. -/
def pairIntersectionMass (centers : Finset FourByThreeClause) : Nat :=
  ∑ pair ∈ centerPairs centers, (commonBallPoints pair).card

/--
Double counting pairs of selected balls through a point expresses their total
intersection mass as the sum of `choose(multiplicity, 2)`.
-/
theorem pairIntersectionMass_eq_sum_choose
    (centers : Finset FourByThreeClause) :
    pairIntersectionMass centers =
      ∑ point : FourByThreeClause,
        (ballCoverMultiplicity centers point).choose 2 := by
  classical
  simp only [pairIntersectionMass, commonBallPoints, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro point _
  let coveringCenters :=
    centers.filter fun center => point ∈ radiusOneBall center
  have hfilter :
      (centerPairs centers).filter
          (fun pair =>
            ∀ center ∈ pair, point ∈ radiusOneBall center) =
        coveringCenters.powersetCard 2 := by
    ext pair
    simp only [centerPairs, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hsubset, hpair_card⟩, hcovered⟩
      refine ⟨?_, hpair_card⟩
      intro center hcenter
      exact Finset.mem_filter.mpr
        ⟨hsubset hcenter, hcovered center hcenter⟩
    · rintro ⟨hsubset, hpair_card⟩
      refine ⟨⟨?_, hpair_card⟩, ?_⟩
      · intro center hcenter
        exact (Finset.mem_filter.mp (hsubset hcenter)).1
      · intro center hcenter
        exact (Finset.mem_filter.mp (hsubset hcenter)).2
  calc
    (∑ pair ∈ centerPairs centers,
        if ∀ center ∈ pair, point ∈ radiusOneBall center then 1 else 0) =
        ((centerPairs centers).filter
          (fun pair =>
            ∀ center ∈ pair, point ∈ radiusOneBall center)).card := by
      rw [Finset.card_filter]
    _ = (coveringCenters.powersetCard 2).card := by rw [hfilter]
    _ = coveringCenters.card.choose 2 :=
      Finset.card_powersetCard 2 coveringCenters
    _ = (ballCoverMultiplicity centers point).choose 2 := rfl

/--
The multiplicity profile on one ternary-code coset contributes exactly one
to the pair-intersection mass.
-/
theorem tenBallCover_sum_choose_on_ternaryCoset
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers)
    (syndrome : TernarySyndrome) :
    ∑ point ∈ ternaryCoset syndrome,
        (ballCoverMultiplicity centers point).choose 2 = 1 := by
  obtain ⟨doublePoint, hdouble, _⟩ :=
    tenBallCover_coset_multiplicity_profile
      centers hcard hcover syndrome
  rw [Finset.sum_eq_single doublePoint]
  · simp [hdouble.2.1]
  · intro point hpoint hne
    simp [hdouble.2.2 point hpoint hne]
  · intro hnot
    exact (hnot hdouble.1).elim

/--
Ten distinct radius-one balls covering the full clause space have total
pairwise intersection mass nine.
-/
theorem tenBallCover_pair_intersection_equation
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers) :
    pairIntersectionMass centers = 9 := by
  rw [pairIntersectionMass_eq_sum_choose]
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(Finset.univ : Finset TernarySyndrome) : Set TernarySyndrome)
        ternaryCoset := by
    intro s _ t _ hst
    exact ternaryCoset_disjoint s t hst
  calc
    (∑ point : FourByThreeClause,
        (ballCoverMultiplicity centers point).choose 2) =
        ∑ syndrome : TernarySyndrome,
          ∑ point ∈ ternaryCoset syndrome,
            (ballCoverMultiplicity centers point).choose 2 := by
      rw [← Finset.sum_biUnion hdisjoint, ternaryCosets_biUnion]
    _ = ∑ _syndrome : TernarySyndrome, 1 := by
      apply Finset.sum_congr rfl
      intro syndrome _
      exact tenBallCover_sum_choose_on_ternaryCoset
        centers hcard hcover syndrome
    _ = 9 := by simp

/-- A two-element center set whose two clauses are at distance `distance`. -/
def HammingPairAtDistance
    (pair : Finset FourByThreeClause) (distance : Nat) : Prop :=
  ((pair ×ˢ pair).filter fun orderedPair =>
    orderedPair.1 ≠ orderedPair.2 ∧
      hammingDistance orderedPair.1 orderedPair.2 = distance).Nonempty

instance instDecidableHammingPairAtDistance
    (pair : Finset FourByThreeClause) (distance : Nat) :
    Decidable (HammingPairAtDistance pair distance) := by
  unfold HammingPairAtDistance
  infer_instance

/-- The number of unordered selected-center pairs at Hamming distance `distance`. -/
def hammingDistancePairCount
    (centers : Finset FourByThreeClause) (distance : Nat) : Nat :=
  ((centerPairs centers).filter fun pair =>
    HammingPairAtDistance pair distance).card

/-- Common points of the two balls centered at `x` and `y`. -/
private theorem commonBallPoints_pair
    (x y : FourByThreeClause) :
    commonBallPoints {x, y} = radiusOneBall x ∩ radiusOneBall y := by
  ext point
  simp [commonBallPoints]

/-- Distance of an unordered two-element set is independent of its ordering. -/
private theorem hammingPairAtDistance_pair_iff
    (x y : FourByThreeClause) (hxy : x ≠ y) (distance : Nat) :
    HammingPairAtDistance {x, y} distance ↔
      hammingDistance x y = distance := by
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hab, hdistance⟩ := hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hdistance
    · simpa only [hammingDistance_comm] using hdistance
    · exact (hab rfl).elim
  · intro hdistance
    exact ⟨(x, y), by simp [hxy, hdistance]⟩

/--
For each unordered pair, its common-ball cardinality is `3` at distance one,
`2` at distance two, and zero otherwise.
-/
private theorem commonBallPoints_card_eq_distance_weights
    (pair : Finset FourByThreeClause)
    (hpair_card : pair.card = 2) :
    (commonBallPoints pair).card =
      (if HammingPairAtDistance pair 1 then 3 else 0) +
      (if HammingPairAtDistance pair 2 then 2 else 0) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hpair_card
  rw [commonBallPoints_pair, radiusOneBall_inter_card]
  generalize hdistance : hammingDistance x y = distance
  have hpositive : 1 ≤ distance := by
    have hne : distance ≠ 0 := by
      intro hzero
      exact hxy ((hammingDistance_eq_zero_iff x y).mp
        (hdistance.trans hzero))
    exact Nat.one_le_iff_ne_zero.mpr hne
  have hle : distance ≤ 4 := by
    simpa [hdistance] using hammingDistance_le_four x y
  have hcases :
      distance = 1 ∨ distance = 2 ∨ distance = 3 ∨ distance = 4 := by
    omega
  rcases hcases with h | h | h | h
  · have hdist : hammingDistance x y = 1 := hdistance.trans h
    have hp1 : HammingPairAtDistance {x, y} 1 :=
      (hammingPairAtDistance_pair_iff x y hxy 1).2 hdist
    have hp2 : ¬HammingPairAtDistance {x, y} 2 := by
      intro hp2
      have := (hammingPairAtDistance_pair_iff x y hxy 2).1 hp2
      omega
    rw [if_pos hp1, if_neg hp2, h]
  · have hdist : hammingDistance x y = 2 := hdistance.trans h
    have hp1 : ¬HammingPairAtDistance {x, y} 1 := by
      intro hp1
      have := (hammingPairAtDistance_pair_iff x y hxy 1).1 hp1
      omega
    have hp2 : HammingPairAtDistance {x, y} 2 :=
      (hammingPairAtDistance_pair_iff x y hxy 2).2 hdist
    rw [if_neg hp1, if_pos hp2, h]
  · have hdist : hammingDistance x y = 3 := hdistance.trans h
    have hp1 : ¬HammingPairAtDistance {x, y} 1 := by
      intro hp1
      have := (hammingPairAtDistance_pair_iff x y hxy 1).1 hp1
      omega
    have hp2 : ¬HammingPairAtDistance {x, y} 2 := by
      intro hp2
      have := (hammingPairAtDistance_pair_iff x y hxy 2).1 hp2
      omega
    rw [if_neg hp1, if_neg hp2, h]
  · have hdist : hammingDistance x y = 4 := hdistance.trans h
    have hp1 : ¬HammingPairAtDistance {x, y} 1 := by
      intro hp1
      have := (hammingPairAtDistance_pair_iff x y hxy 1).1 hp1
      omega
    have hp2 : ¬HammingPairAtDistance {x, y} 2 := by
      intro hp2
      have := (hammingPairAtDistance_pair_iff x y hxy 2).1 hp2
      omega
    rw [if_neg hp1, if_neg hp2, h]

/--
For an arbitrary finite set of distinct centers, pair-intersection mass is
`3 n₁ + 2 n₂`, where `n_d` counts unordered pairs at distance `d`.
-/
theorem pairIntersectionMass_eq_distancePairCounts
    (centers : Finset FourByThreeClause) :
    pairIntersectionMass centers =
      3 * hammingDistancePairCount centers 1 +
        2 * hammingDistancePairCount centers 2 := by
  classical
  unfold pairIntersectionMass
  calc
    (∑ pair ∈ centerPairs centers, (commonBallPoints pair).card) =
        ∑ pair ∈ centerPairs centers,
          ((if HammingPairAtDistance pair 1 then 3 else 0) +
            (if HammingPairAtDistance pair 2 then 2 else 0)) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact commonBallPoints_card_eq_distance_weights pair
        (Finset.mem_powersetCard.mp hpair).2
    _ =
        (∑ pair ∈ centerPairs centers,
          if HammingPairAtDistance pair 1 then 3 else 0) +
        ∑ pair ∈ centerPairs centers,
          if HammingPairAtDistance pair 2 then 2 else 0 := by
      rw [Finset.sum_add_distrib]
    _ =
        3 * hammingDistancePairCount centers 1 +
          2 * hammingDistancePairCount centers 2 := by
      simp only [hammingDistancePairCount, Finset.card_filter]
      congr 1 <;>
        rw [Finset.mul_sum] <;>
        apply Finset.sum_congr rfl <;>
        intro pair _ <;>
        split <;> simp_all

/--
The ten-ball-cover double count:

`3 n₁ + 2 n₂ = 9`.
-/
theorem tenBallCover_distance_equation
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers) :
    3 * hammingDistancePairCount centers 1 +
      2 * hammingDistancePairCount centers 2 = 9 := by
  rw [← pairIntersectionMass_eq_distancePairCounts]
  exact tenBallCover_pair_intersection_equation centers hcard hcover

/-- The selected clauses in one page/question block. -/
def pageQuestionBlock
    (centers : Finset FourByThreeClause)
    (page : FourByThreePlayer) (question : FourByThreeQuestion) :
    Finset FourByThreeClause :=
  centers.filter fun center => center page = question

/--
Total number of unordered clause pairs which agree on a page, summed over
the four pages.
-/
def pageAgreementMass (centers : Finset FourByThreeClause) : Nat :=
  ∑ page : FourByThreePlayer,
    ∑ question : FourByThreeQuestion,
      (pageQuestionBlock centers page question).card.choose 2

/-- The three question blocks on a fixed page partition the selected clauses. -/
theorem sum_pageQuestionBlock_card
    (centers : Finset FourByThreeClause) (page : FourByThreePlayer) :
    ∑ question : FourByThreeQuestion,
      (pageQuestionBlock centers page question).card = centers.card := by
  classical
  have hfiber :=
    Finset.sum_fiberwise centers
      (fun center => center page) (fun _center => (1 : Nat))
  simpa [pageQuestionBlock] using hfiber

/--
Among three blocks containing ten objects in total, the sum of the three
unordered-pair counts is at least twelve.  This is the convexity bound whose
equality profile is `(4, 3, 3)`.
-/
private theorem three_block_choose_two_ge_twelve
    (a b c : Nat) (hsum : a + b + c = 10) :
    12 ≤ a.choose 2 + b.choose 2 + c.choose 2 := by
  have hsumQ : (a : ℚ) + b + c = 10 := by
    exact_mod_cast hsum
  have hsquare₁ : 0 ≤ ((a : ℚ) - b) ^ 2 := sq_nonneg _
  have hsquare₂ : 0 ≤ ((b : ℚ) - c) ^ 2 := sq_nonneg _
  have hsquare₃ : 0 ≤ ((c : ℚ) - a) ^ 2 := sq_nonneg _
  have hchoose :
      ((a.choose 2 + b.choose 2 + c.choose 2 : Nat) : ℚ) =
        ((a : ℚ) * (a - 1) + (b : ℚ) * (b - 1) +
          (c : ℚ) * (c - 1)) / 2 := by
    push_cast
    rw [Nat.cast_choose_two, Nat.cast_choose_two, Nat.cast_choose_two]
    ring
  by_contra hnot
  have hle : a.choose 2 + b.choose 2 + c.choose 2 ≤ 11 := by
    omega
  have hleQ :
      ((a.choose 2 + b.choose 2 + c.choose 2 : Nat) : ℚ) ≤ 11 := by
    exact_mod_cast hle
  rw [hchoose] at hleQ
  nlinarith

/-- A ten-clause support has at least twelve agreeing pairs on each page. -/
theorem tenCenters_pageAgreement_ge_twelve
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (page : FourByThreePlayer) :
    12 ≤
      ∑ question : FourByThreeQuestion,
        (pageQuestionBlock centers page question).card.choose 2 := by
  let a := (pageQuestionBlock centers page 0).card
  let b := (pageQuestionBlock centers page 1).card
  let c := (pageQuestionBlock centers page 2).card
  have hsumQuestions :=
    sum_pageQuestionBlock_card centers page
  have hsum : a + b + c = 10 := by
    simpa [a, b, c, Fin.sum_univ_succ, hcard, add_assoc] using
      hsumQuestions
  have hbound := three_block_choose_two_ge_twelve a b c hsum
  simpa [a, b, c, Fin.sum_univ_succ, add_assoc] using hbound

/--
Across four pages, a ten-clause support has at least 48 coordinate
agreements over unordered clause pairs.
-/
theorem tenCenters_pageAgreementMass_ge_fortyEight
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10) :
    48 ≤ pageAgreementMass centers := by
  unfold pageAgreementMass
  calc
    48 = ∑ _page : FourByThreePlayer, 12 := by norm_num
    _ ≤ ∑ page : FourByThreePlayer,
        ∑ question : FourByThreeQuestion,
          (pageQuestionBlock centers page question).card.choose 2 :=
      Finset.sum_le_sum fun page _ =>
        tenCenters_pageAgreement_ge_twelve centers hcard page

/-- All centers in `pair` carry the same question on `page`. -/
def PairAgreesOnPage
    (pair : Finset FourByThreeClause) (page : FourByThreePlayer) : Prop :=
  ∀ x ∈ pair, ∀ y ∈ pair, x page = y page

noncomputable instance instDecidablePairAgreesOnPage
    (pair : Finset FourByThreeClause) (page : FourByThreePlayer) :
    Decidable (PairAgreesOnPage pair page) :=
  Classical.propDecidable _

/-- Number of unordered selected-center pairs agreeing on one page. -/
noncomputable def pageAgreementPairCount
    (centers : Finset FourByThreeClause) (page : FourByThreePlayer) : Nat :=
  ((centerPairs centers).filter fun pair =>
    PairAgreesOnPage pair page).card

/-- A two-element pair agrees on a page exactly when its two entries do. -/
private theorem pairAgreesOnPage_pair_iff
    (x y : FourByThreeClause) (page : FourByThreePlayer) :
    PairAgreesOnPage {x, y} page ↔ x page = y page := by
  constructor
  · intro h
    exact h x (by simp) y (by simp)
  · intro h a ha b hb
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact h
    · exact h.symm
    · rfl

/--
For a fixed two-element pair, exactly one question block contains the pair
when it agrees on the page, and no question block does otherwise.
-/
private theorem sum_question_pair_subset_indicator
    (centers : Finset FourByThreeClause)
    (page : FourByThreePlayer)
    (pair : Finset FourByThreeClause)
    (hpair : pair ∈ centerPairs centers) :
    ∑ question : FourByThreeQuestion,
        (if pair ⊆ pageQuestionBlock centers page question then 1 else 0) =
      if PairAgreesOnPage pair page then 1 else 0 := by
  have hpair_card := (Finset.mem_powersetCard.mp hpair).2
  have hpair_subset := (Finset.mem_powersetCard.mp hpair).1
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hpair_card
  have hx : x ∈ centers := hpair_subset (by simp)
  have hy : y ∈ centers := hpair_subset (by simp)
  have hsubset :
      ∀ question : FourByThreeQuestion,
        ({x, y} : Finset FourByThreeClause) ⊆
            pageQuestionBlock centers page question ↔
          x page = question ∧ y page = question := by
    intro question
    constructor
    · intro h
      exact ⟨
        (Finset.mem_filter.mp (h (by simp))).2,
        (Finset.mem_filter.mp (h (by simp))).2⟩
    · rintro ⟨hxq, hyq⟩ center hcenter
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcenter
      rcases hcenter with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨hx, hxq⟩
      · exact Finset.mem_filter.mpr ⟨hy, hyq⟩
  have hrewrite :
      (∑ question : FourByThreeQuestion,
        if ({x, y} : Finset FourByThreeClause) ⊆
            pageQuestionBlock centers page question then 1 else 0) =
      ∑ question : FourByThreeQuestion,
        if x page = question ∧ y page = question then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro question _
    exact if_congr (hsubset question) rfl rfl
  rw [hrewrite]
  have hagree := pairAgreesOnPage_pair_iff x y page
  by_cases hxyPage : x page = y page
  · rw [if_pos (hagree.2 hxyPage)]
    calc
      (∑ question : FourByThreeQuestion,
        if x page = question ∧ y page = question then 1 else 0) =
          (if x page = x page ∧ y page = x page then 1 else 0) := by
        apply Finset.sum_eq_single (x page)
        · intro question _ hquestion
          split
          · rename_i hboth
            exact (hquestion hboth.1.symm).elim
          · rfl
        · simp
      _ = 1 := by simp [hxyPage]
  · rw [if_neg (fun hagrees => hxyPage (hagree.1 hagrees))]
    apply Finset.sum_eq_zero
    intro question _
    split
    · rename_i hboth
      exact (hxyPage (hboth.1.trans hboth.2.symm)).elim
    · rfl

/--
Counting agreeing unordered pairs by question blocks or directly by pairs
gives the same result on each page.
-/
theorem sum_choose_pageQuestionBlock_eq_pageAgreementPairCount
    (centers : Finset FourByThreeClause) (page : FourByThreePlayer) :
    (∑ question : FourByThreeQuestion,
        (pageQuestionBlock centers page question).card.choose 2) =
      pageAgreementPairCount centers page := by
  classical
  have hpowerset :
      ∀ question : FourByThreeQuestion,
        (pageQuestionBlock centers page question).powersetCard 2 =
          (centerPairs centers).filter fun pair =>
            pair ⊆ pageQuestionBlock centers page question := by
    intro question
    ext pair
    simp only [Finset.mem_powersetCard, Finset.mem_filter, centerPairs]
    constructor
    · rintro ⟨hsubsetBlock, hcardPair⟩
      refine ⟨⟨?_, hcardPair⟩, hsubsetBlock⟩
      intro center hcenter
      exact (Finset.mem_filter.mp (hsubsetBlock hcenter)).1
    · rintro ⟨⟨_, hcardPair⟩, hsubsetBlock⟩
      exact ⟨hsubsetBlock, hcardPair⟩
  calc
    (∑ question : FourByThreeQuestion,
        (pageQuestionBlock centers page question).card.choose 2) =
        ∑ question : FourByThreeQuestion,
          ((pageQuestionBlock centers page question).powersetCard 2).card := by
      apply Finset.sum_congr rfl
      intro question _
      exact (Finset.card_powersetCard 2
        (pageQuestionBlock centers page question)).symm
    _ = ∑ question : FourByThreeQuestion,
        ((centerPairs centers).filter fun pair =>
          pair ⊆ pageQuestionBlock centers page question).card := by
      apply Finset.sum_congr rfl
      intro question _
      rw [hpowerset question]
    _ = ∑ question : FourByThreeQuestion,
        ∑ pair ∈ centerPairs centers,
          if pair ⊆ pageQuestionBlock centers page question then 1 else 0 := by
      simp only [Finset.card_filter]
    _ = ∑ pair ∈ centerPairs centers,
        ∑ question : FourByThreeQuestion,
          if pair ⊆ pageQuestionBlock centers page question then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ pair ∈ centerPairs centers,
        if PairAgreesOnPage pair page then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact sum_question_pair_subset_indicator centers page pair hpair
    _ = pageAgreementPairCount centers page := by
      rw [pageAgreementPairCount, Finset.card_filter]

/-- The block definition of agreement mass equals its pair-count definition. -/
theorem pageAgreementMass_eq_sum_pairCount
    (centers : Finset FourByThreeClause) :
    pageAgreementMass centers =
      ∑ page : FourByThreePlayer,
        pageAgreementPairCount centers page := by
  unfold pageAgreementMass
  apply Finset.sum_congr rfl
  intro page _
  exact sum_choose_pageQuestionBlock_eq_pageAgreementPairCount centers page

/--
For a two-element pair, the number of agreeing coordinates is four minus
its Hamming distance.
-/
private theorem sum_page_agreement_indicator_eq_four_sub_distance
    (x y : FourByThreeClause) :
    (∑ page : FourByThreePlayer,
        if PairAgreesOnPage {x, y} page then 1 else 0) =
      4 - hammingDistance x y := by
  have hindicators :
      (∑ page : FourByThreePlayer,
        if PairAgreesOnPage {x, y} page then 1 else 0) =
      ∑ page : FourByThreePlayer,
        if x page = y page then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro page _
    exact if_congr (pairAgreesOnPage_pair_iff x y page) rfl rfl
  rw [hindicators]
  have hpartition :
      ((Finset.univ : Finset FourByThreePlayer).filter
          fun page => x page = y page).card +
        ((Finset.univ : Finset FourByThreePlayer).filter
          fun page => ¬x page = y page).card =
        (Finset.univ : Finset FourByThreePlayer).card :=
    Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset FourByThreePlayer))
      (fun page => x page = y page)
  have hdistance :
      ((Finset.univ : Finset FourByThreePlayer).filter
          fun page => ¬x page = y page).card =
        hammingDistance x y := by
    unfold hammingDistance
    congr 1
  have huniv :
      (Finset.univ : Finset FourByThreePlayer).card = 4 := by
    simp
  rw [← Finset.card_filter]
  omega

/--
The agreement contribution of one unordered pair is `3`, `2`, `1`, or `0`
at Hamming distance `1`, `2`, `3`, or `4`.
-/
private theorem pair_page_agreement_eq_distance_weights
    (pair : Finset FourByThreeClause)
    (hpair_card : pair.card = 2) :
    (∑ page : FourByThreePlayer,
        if PairAgreesOnPage pair page then 1 else 0) =
      3 * (if HammingPairAtDistance pair 1 then 1 else 0) +
        2 * (if HammingPairAtDistance pair 2 then 1 else 0) +
        (if HammingPairAtDistance pair 3 then 1 else 0) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hpair_card
  rw [sum_page_agreement_indicator_eq_four_sub_distance
    x y]
  have hp_of_eq :
      ∀ distance : Nat,
        hammingDistance x y = distance →
          HammingPairAtDistance {x, y} distance := by
    intro distance hdistance
    exact (hammingPairAtDistance_pair_iff x y hxy distance).2 hdistance
  have hnp_of_ne :
      ∀ distance : Nat,
        hammingDistance x y ≠ distance →
          ¬HammingPairAtDistance {x, y} distance := by
    intro distance hne hp
    exact hne ((hammingPairAtDistance_pair_iff x y hxy distance).1 hp)
  have hpositive : 1 ≤ hammingDistance x y :=
    Nat.one_le_iff_ne_zero.mpr fun hzero =>
      hxy ((hammingDistance_eq_zero_iff x y).mp hzero)
  have hle := hammingDistance_le_four x y
  have hcases :
      hammingDistance x y = 1 ∨
        hammingDistance x y = 2 ∨
        hammingDistance x y = 3 ∨
        hammingDistance x y = 4 := by
    omega
  rcases hcases with h | h | h | h
  · rw [if_pos (hp_of_eq 1 h),
      if_neg (hnp_of_ne 2 (by omega)),
      if_neg (hnp_of_ne 3 (by omega)), h]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_pos (hp_of_eq 2 h),
      if_neg (hnp_of_ne 3 (by omega)), h]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_neg (hnp_of_ne 2 (by omega)),
      if_pos (hp_of_eq 3 h), h]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_neg (hnp_of_ne 2 (by omega)),
      if_neg (hnp_of_ne 3 (by omega)), h]

/--
The page-block agreement mass is exactly
`3 n₁ + 2 n₂ + n₃`.
-/
theorem pageAgreementMass_eq_distancePairCounts
    (centers : Finset FourByThreeClause) :
    pageAgreementMass centers =
      3 * hammingDistancePairCount centers 1 +
        2 * hammingDistancePairCount centers 2 +
        hammingDistancePairCount centers 3 := by
  classical
  rw [pageAgreementMass_eq_sum_pairCount]
  simp only [pageAgreementPairCount, Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ pair ∈ centerPairs centers,
        ∑ page : FourByThreePlayer,
          if PairAgreesOnPage pair page then 1 else 0) =
      ∑ pair ∈ centerPairs centers,
        (3 * (if HammingPairAtDistance pair 1 then 1 else 0) +
          2 * (if HammingPairAtDistance pair 2 then 1 else 0) +
          (if HammingPairAtDistance pair 3 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact pair_page_agreement_eq_distance_weights pair
        (Finset.mem_powersetCard.mp hpair).2
    _ =
        (∑ pair ∈ centerPairs centers,
          3 * (if HammingPairAtDistance pair 1 then 1 else 0)) +
        (∑ pair ∈ centerPairs centers,
          2 * (if HammingPairAtDistance pair 2 then 1 else 0)) +
        ∑ pair ∈ centerPairs centers,
          (if HammingPairAtDistance pair 3 then 1 else 0) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ =
        3 * hammingDistancePairCount centers 1 +
          2 * hammingDistancePairCount centers 2 +
          hammingDistancePairCount centers 3 := by
      simp only [hammingDistancePairCount, Finset.card_filter]
      rw [Finset.mul_sum, Finset.mul_sum]

/-- Every unordered pair of distinct four-by-three clauses has one distance
in `{1,2,3,4}`. -/
private theorem pair_distance_indicator_sum
    (pair : Finset FourByThreeClause)
    (hpair_card : pair.card = 2) :
    (if HammingPairAtDistance pair 1 then 1 else 0) +
      (if HammingPairAtDistance pair 2 then 1 else 0) +
      (if HammingPairAtDistance pair 3 then 1 else 0) +
      (if HammingPairAtDistance pair 4 then 1 else 0) = 1 := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hpair_card
  have hp_of_eq :
      ∀ distance : Nat,
        hammingDistance x y = distance →
          HammingPairAtDistance {x, y} distance := by
    intro distance hdistance
    exact (hammingPairAtDistance_pair_iff x y hxy distance).2 hdistance
  have hnp_of_ne :
      ∀ distance : Nat,
        hammingDistance x y ≠ distance →
          ¬HammingPairAtDistance {x, y} distance := by
    intro distance hne hp
    exact hne ((hammingPairAtDistance_pair_iff x y hxy distance).1 hp)
  have hpositive : 1 ≤ hammingDistance x y := by
    exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
      hxy ((hammingDistance_eq_zero_iff x y).mp hzero)
  have hle := hammingDistance_le_four x y
  have hcases :
      hammingDistance x y = 1 ∨
        hammingDistance x y = 2 ∨
        hammingDistance x y = 3 ∨
        hammingDistance x y = 4 := by
    omega
  rcases hcases with h | h | h | h
  · rw [if_pos (hp_of_eq 1 h),
      if_neg (hnp_of_ne 2 (by omega)),
      if_neg (hnp_of_ne 3 (by omega)),
      if_neg (hnp_of_ne 4 (by omega))]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_pos (hp_of_eq 2 h),
      if_neg (hnp_of_ne 3 (by omega)),
      if_neg (hnp_of_ne 4 (by omega))]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_neg (hnp_of_ne 2 (by omega)),
      if_pos (hp_of_eq 3 h),
      if_neg (hnp_of_ne 4 (by omega))]
  · rw [if_neg (hnp_of_ne 1 (by omega)),
      if_neg (hnp_of_ne 2 (by omega)),
      if_neg (hnp_of_ne 3 (by omega)),
      if_pos (hp_of_eq 4 h)]

/--
The distance-one through distance-four pair counts partition all unordered
pairs of selected distinct centers.
-/
theorem hammingDistancePairCount_partition
    (centers : Finset FourByThreeClause) :
    hammingDistancePairCount centers 1 +
      hammingDistancePairCount centers 2 +
      hammingDistancePairCount centers 3 +
      hammingDistancePairCount centers 4 =
        centers.card.choose 2 := by
  classical
  simp only [hammingDistancePairCount, Finset.card_filter]
  calc
    (∑ pair ∈ centerPairs centers,
        if HammingPairAtDistance pair 1 then 1 else 0) +
          (∑ pair ∈ centerPairs centers,
            if HammingPairAtDistance pair 2 then 1 else 0) +
          (∑ pair ∈ centerPairs centers,
            if HammingPairAtDistance pair 3 then 1 else 0) +
          (∑ pair ∈ centerPairs centers,
            if HammingPairAtDistance pair 4 then 1 else 0) =
        ∑ pair ∈ centerPairs centers,
          ((if HammingPairAtDistance pair 1 then 1 else 0) +
            (if HammingPairAtDistance pair 2 then 1 else 0) +
            (if HammingPairAtDistance pair 3 then 1 else 0) +
            (if HammingPairAtDistance pair 4 then 1 else 0)) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_add_distrib]
    _ = ∑ _pair ∈ centerPairs centers, 1 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact pair_distance_indicator_sum pair
        (Finset.mem_powersetCard.mp hpair).2
    _ = (centerPairs centers).card := by simp
    _ = centers.card.choose 2 := by
      exact Finset.card_powersetCard 2 centers

/--
The nonzero off-diagonal graph of the centered incidence Gram matrix has at
most six edges for a ten-ball cover.  Its edges are precisely the pairs at
distances one, two, and four.
-/
theorem tenBallCover_nonzeroGramEdgeCount_le_six
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers) :
    hammingDistancePairCount centers 1 +
        hammingDistancePairCount centers 2 +
        hammingDistancePairCount centers 4 ≤ 6 := by
  have hcoverEquation :=
    tenBallCover_distance_equation centers hcard hcover
  have hpartition :=
    hammingDistancePairCount_partition centers
  rw [hcard] at hpartition
  norm_num [Nat.choose] at hpartition
  have hagreement :=
    tenCenters_pageAgreementMass_ge_fortyEight centers hcard
  rw [pageAgreementMass_eq_distancePairCounts] at hagreement
  omega

/--
Arithmetic endpoint of the ten-ball-cover obstruction.

The rank-nine, nullity-one Gram argument for a full circuit makes its nonzero
off-diagonal graph connected, so on ten vertices it has at least nine edges.
This contradicts the structural upper bound of six proved above.
-/
theorem tenBallCover_structural_contradiction
    (centers : Finset FourByThreeClause)
    (hcard : centers.card = 10)
    (hcover : RadiusOneBallCover centers)
    (hGramConnected :
      9 ≤ hammingDistancePairCount centers 1 +
        hammingDistancePairCount centers 2 +
        hammingDistancePairCount centers 4) :
    False := by
  have hupper :=
    tenBallCover_nonzeroGramEdgeCount_le_six centers hcard hcover
  omega

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.FourColorForest
public import XORGameFormalization.SafeCenter
public import XORGameFormalization.SelectedBlockLayout

/-!
# Safe-center selected-block systems

A safe center selects one question block on each of the four pages.  The
signature of a clause is its set of agreements with the center.  Safety says
that these signatures have size at most two, while the integer relation gives
color balance.  This module packages the exact reduction from the Hamming
geometry to the abstract four-color forest problem.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- The player coordinates on which a clause agrees with a center. -/
def safeCenterColorSignature
    {E : Type uE} (query : E → FourByThreeClause)
    (center : FourByThreeClause) (clause : E) :
    Finset FourByThreePlayer :=
  Finset.univ.filter fun player => query clause player = center player

@[simp]
theorem mem_safeCenterColorSignature
    {E : Type uE} (query : E → FourByThreeClause)
    (center : FourByThreeClause) (clause : E)
    (player : FourByThreePlayer) :
    player ∈ safeCenterColorSignature query center clause ↔
      query clause player = center player := by
  simp [safeCenterColorSignature]

/-- Agreement coordinates are the complement of Hamming-support coordinates. -/
theorem safeCenterColorSignature_eq_compl_hammingSupport
    {E : Type uE} (query : E → FourByThreeClause)
    (center : FourByThreeClause) (clause : E) :
    safeCenterColorSignature query center clause =
      (hammingSupport center (query clause))ᶜ := by
  ext player
  simp [safeCenterColorSignature, hammingSupport, eq_comm]

/-- Signature size is four minus Hamming distance. -/
theorem safeCenterColorSignature_card
    {E : Type uE} (query : E → FourByThreeClause)
    (center : FourByThreeClause) (clause : E) :
    (safeCenterColorSignature query center clause).card =
      4 - hammingDistance center (query clause) := by
  rw [safeCenterColorSignature_eq_compl_hammingSupport,
    Finset.card_compl, hammingSupport_card]
  rfl

/-- Safety makes every center-agreement signature have size at most two. -/
theorem safeCenterColorSignature_card_le_two
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (clause : E) :
    (safeCenterColorSignature query center clause).card ≤ 2 := by
  have hsafe : 2 ≤ hammingDistance center (query clause) := by
    have hcenter' := (Finset.mem_filter.mp hcenter).2
    exact hcenter' (query clause)
      (Finset.mem_image.mpr ⟨clause, Finset.mem_univ _, rfl⟩)
  rw [safeCenterColorSignature_card]
  omega

/-- If a safe center does not have even distance from every clause, then one
clause agrees with it in exactly one coordinate. -/
theorem exists_singleton_safeCenterColorSignature_of_not_evenSupportDistances
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (hodd : ¬ EvenSupportDistances query center) :
    ∃ clause color,
      safeCenterColorSignature query center clause = {color} := by
  unfold EvenSupportDistances at hodd
  push Not at hodd
  obtain ⟨clause, hclause⟩ := hodd
  have hsafe : 2 ≤ hammingDistance center (query clause) := by
    exact (Finset.mem_filter.mp hcenter).2 (query clause)
      (Finset.mem_image.mpr ⟨clause, Finset.mem_univ _, rfl⟩)
  have hupper := hammingDistance_le_four center (query clause)
  have hdistance : hammingDistance center (query clause) = 3 := by
    interval_cases h : hammingDistance center (query clause)
    · exfalso
      exact hclause ⟨1, rfl⟩
    · rfl
    · exfalso
      exact hclause ⟨2, rfl⟩
  have hcard :
      (safeCenterColorSignature query center clause).card = 1 := by
    rw [safeCenterColorSignature_card, hdistance]
  obtain ⟨color, hsignature⟩ := Finset.card_eq_one.mp hcard
  exact ⟨clause, color, hsignature⟩

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
    _ = Fintype.card
        {occurrence : PositiveOccurrence y //
          positiveOccurrenceQuestion query player occurrence = question} := by
      symm
      exact Fintype.card_ofFinset _ (by
        intro occurrence
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          positiveOccurrenceQuestion]
        rfl)
    _ = Fintype.card
        {occurrence : NegativeOccurrence y //
          negativeOccurrenceQuestion query player occurrence = question} :=
      positiveOccurrenceQuestion_fiber_card_eq_negative
        query y hy player question
    _ = _ := by
      exact Fintype.card_ofFinset _ (by
        intro occurrence
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          negativeOccurrenceQuestion]
        rfl)

/-- The balanced four-color signature system selected by a safe center. -/
def safeCenterColorSignatureSystem
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query)) :
    ColorSignatureSystem FourByThreePlayer
      (PositiveOccurrence y) (NegativeOccurrence y) where
  positiveSignature occurrence :=
    safeCenterColorSignature query center occurrence.1
  negativeSignature occurrence :=
    safeCenterColorSignature query center occurrence.1
  positive_card_le_two occurrence :=
    safeCenterColorSignature_card_le_two
      query center hcenter occurrence.1
  negative_card_le_two occurrence :=
    safeCenterColorSignature_card_le_two
      query center hcenter occurrence.1
  balanced := by
    intro player
    simpa [safeCenterColorSignature] using
      occurrenceQuestion_filter_card_eq
        query y hy player (center player)

/-- With nonzero coefficients, an odd safe-center distance produces a
singleton vertex on one side of the occurrence signature system. -/
theorem exists_singletonOccurrence_of_not_evenSupportDistances
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (hcoeff : ∀ clause, y clause ≠ 0)
    (hodd : ¬ EvenSupportDistances query center) :
    (∃ positive color,
        (safeCenterColorSignatureSystem query y hy center hcenter).positiveSignature
            positive = {color}) ∨
      ∃ negative color,
        (safeCenterColorSignatureSystem query y hy center hcenter).negativeSignature
            negative = {color} := by
  obtain ⟨clause, color, hsignature⟩ :=
    exists_singleton_safeCenterColorSignature_of_not_evenSupportDistances
      query center hcenter hodd
  rcases lt_or_gt_of_ne (hcoeff clause) with hnegative | hpositive
  · right
    have hcopy : 0 < (-y clause).toNat := by
      omega
    exact ⟨⟨clause, ⟨0, hcopy⟩⟩, color, hsignature⟩
  · left
    have hcopy : 0 < (y clause).toNat := by
      omega
    exact ⟨⟨clause, ⟨0, hcopy⟩⟩, color, hsignature⟩

/--
A forest matching of the safe-center signature system is exactly a
selected-block certificate for the four center questions.
-/
def selectedBlockCertificateOfSafeCenterMatching
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (matching :
      ColorwiseMatching
        (safeCenterColorSignatureSystem query y hy center hcenter))
    (hforest : matching.IsBipartiteLinearForest) :
    SelectedBlockLinearForestCertificate query y where
  selectedQuestion := center
  Match := matching.Match
  match_mem := by
    intro player positive negative hmatch
    simpa [safeCenterColorSignatureSystem,
      safeCenterColorSignature] using matching.match_mem hmatch
  positive_unique := by
    intro player positive hpositive
    apply matching.positive_unique
    simpa [safeCenterColorSignatureSystem,
      safeCenterColorSignature] using hpositive
  negative_unique := by
    intro player negative hnegative
    apply matching.negative_unique
    simpa [safeCenterColorSignatureSystem,
      safeCenterColorSignature] using hnegative
  linear_forest := by
    have hgraph :
        selectedBlockSimpleGraph matching.Match = matching.simpleGraph :=
      selectedBlockSimpleGraph_comp_surjective
        matching id Function.surjective_id
    constructor
    · rw [hgraph]
      exact hforest.1
    · intro vertex
      rw [hgraph, ← Set.fintypeCard_eq_ncard,
        matching.simpleGraph.card_neighborSet_eq_degree]
      exact hforest.2 vertex

/-- A safe-center forest matching yields an exact-multiplicity lift. -/
theorem hasExactMultiplicityBalancedLift_of_safeCenterLinearForestMatching
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (hmatching :
      (safeCenterColorSignatureSystem query y hy center hcenter).HasLinearForestMatching) :
    HasExactMultiplicityBalancedLift query y := by
  obtain ⟨matching, hforest⟩ := hmatching
  exact selectedBlockLinearForest_exactMultiplicityBalancedLift
    query y hy
      (selectedBlockCertificateOfSafeCenterMatching
        query y hy center hcenter matching hforest)

/-- A non-even safe center always gives an exact lift when every coefficient
is nonzero.  The odd-distance clause supplies a singleton signature, and the
four-color singleton-escape theorem supplies the required forest matching. -/
theorem hasExactMultiplicityBalancedLift_of_odd_safeCenter
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause) (y : E → ℤ)
    (hy : IsIntegerRelation query y)
    (center : FourByThreeClause)
    (hcenter : center ∈ safeCenters (Finset.univ.image query))
    (hcoeff : ∀ clause, y clause ≠ 0)
    (hodd : ¬ EvenSupportDistances query center) :
    HasExactMultiplicityBalancedLift query y := by
  let system := safeCenterColorSignatureSystem query y hy center hcenter
  have hsingleton :
      (∃ positive color,
          system.positiveSignature positive = {color}) ∨
        ∃ negative color,
          system.negativeSignature negative = {color} := by
    simpa [system] using
      exists_singletonOccurrence_of_not_evenSupportDistances
        query y hy center hcenter hcoeff hodd
  have hmatching : system.HasLinearForestMatching :=
    ColorSignatureSystem.linearForestMatching_of_singleton
      system hsingleton
  exact hasExactMultiplicityBalancedLift_of_safeCenterLinearForestMatching
    query y hy center hcenter (by simpa [system] using hmatching)

end

end XORGame
end QIT

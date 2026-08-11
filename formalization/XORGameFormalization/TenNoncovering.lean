/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.BoundaryFibers
public import XORGameFormalization.GramConnectivity
public import XORGameFormalization.SafeHoleExcess

/-!
# Structural ten-clause noncoverage

This module proves the geometry core of the ten-clause obstruction without
enumerating supports.  The proof first forces at least seven layer-two
clauses about every safe center, then uses disjoint safe-hole neighborhoods
and the global coverage-excess identity to show that the safe center is
unique.  Finally the six two-coordinate layer fibers each require two
same-support clauses, contradicting a ten-clause support.
-/

@[expose] public section

namespace QIT.XORGame

universe uE

noncomputable section

/-- The support clauses at Hamming distance two from `center`. -/
def layerTwoClauseCount
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause) : Nat :=
  (support.filter fun clause =>
    hammingDistance center clause = 2).card

/-- The six two-coordinate supports in four coordinates. -/
def coordinateSupportIndices : Finset (Finset FourByThreePlayer) :=
  (Finset.univ : Finset FourByThreePlayer).powersetCard 2

@[simp]
theorem coordinateSupportIndices_card :
    coordinateSupportIndices.card = 6 := by
  norm_num [coordinateSupportIndices, Finset.card_powersetCard, Nat.choose]

/-- Layer-two points with one fixed two-coordinate support. -/
def layerTwoCoordinateFiber
    (center : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer) :
    Finset FourByThreeClause :=
  Finset.univ.filter fun point =>
    hammingSupport center point = coordinates

/-- Support clauses with one fixed coordinate support relative to a center. -/
def sameCoordinateSupportClauses
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer) :
    Finset FourByThreeClause :=
  support.filter fun clause =>
    hammingSupport center clause = coordinates

/-- A two-coordinate layer fiber has `2^2 = 4` label assignments. -/
theorem layerTwoCoordinateFiber_card_eq_four
    (center : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer)
    (hcoordinates : coordinates.card = 2) :
    (layerTwoCoordinateFiber center coordinates).card = 4 := by
  classical
  let Labeling :=
    (coordinate : coordinates) →
      {question : FourByThreeQuestion //
        question ≠ center coordinate}
  let encode :
      ↥(layerTwoCoordinateFiber center coordinates) → Labeling :=
    fun point coordinate =>
      ⟨point.1 coordinate, by
        have hsupport :
            hammingSupport center point.1 = coordinates :=
          (Finset.mem_filter.mp point.2).2
        have hmem :
            coordinate.1 ∈ hammingSupport center point.1 := by
          rw [hsupport]
          exact coordinate.2
        exact Ne.symm (by
          simpa [hammingSupport] using hmem)⟩
  let decode :
      Labeling → ↥(layerTwoCoordinateFiber center coordinates) :=
    fun labeling =>
      ⟨fun coordinate =>
          if h : coordinate ∈ coordinates then
            (labeling ⟨coordinate, h⟩).1
          else center coordinate,
        by
          apply Finset.mem_filter.mpr
          constructor
          · exact Finset.mem_univ _
          · ext coordinate
            by_cases hcoordinate : coordinate ∈ coordinates
            · have hne :
                  (labeling ⟨coordinate, hcoordinate⟩).1 ≠
                    center coordinate :=
                (labeling ⟨coordinate, hcoordinate⟩).2
              simp [hammingSupport, hcoordinate, Ne.symm hne]
            · simp [hammingSupport, hcoordinate]⟩
  let equivalence :
      ↥(layerTwoCoordinateFiber center coordinates) ≃ Labeling := {
    toFun := encode
    invFun := decode
    left_inv := by
      intro point
      apply Subtype.ext
      funext coordinate
      by_cases hcoordinate : coordinate ∈ coordinates
      · simp [encode, decode, hcoordinate]
      · have hsupport :
            hammingSupport center point.1 = coordinates :=
          (Finset.mem_filter.mp point.2).2
        have hnot :
            coordinate ∉ hammingSupport center point.1 := by
          rw [hsupport]
          exact hcoordinate
        have heq : center coordinate = point.1 coordinate := by
          simpa [hammingSupport] using hnot
        simp [decode, hcoordinate, heq]
    right_inv := by
      intro labeling
      funext coordinate
      apply Subtype.ext
      simp [encode, decode, coordinate.2]
  }
  have hchoiceCard :
      ∀ coordinate : coordinates,
        Fintype.card
          {question : FourByThreeQuestion //
            question ≠ center coordinate} = 2 := by
    intro coordinate
    rw [Fintype.card_subtype]
    have hfilter :
        (Finset.univ.filter fun question : FourByThreeQuestion =>
          question ≠ center coordinate) =
          Finset.univ.erase (center coordinate) := by
      ext question
      simp
    rw [hfilter, Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
  calc
    (layerTwoCoordinateFiber center coordinates).card =
        Fintype.card ↥(layerTwoCoordinateFiber center coordinates) := by
      simp
    _ = Fintype.card Labeling :=
      Fintype.card_congr equivalence
    _ =
        ∏ coordinate : coordinates,
          Fintype.card
            {question : FourByThreeQuestion //
              question ≠ center coordinate} := Fintype.card_pi
    _ = ∏ _coordinate : coordinates, 2 := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact hchoiceCard coordinate
    _ = 4 := by
      simp [hcoordinates]

/-- A ternary question different from each of two prescribed questions exists. -/
private theorem exists_question_ne_two
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

/-- A chosen ternary question avoiding two prescribed values. -/
private noncomputable def avoidTwoQuestions
    (x y : FourByThreeQuestion) : FourByThreeQuestion :=
  Classical.choose (exists_question_ne_two x y)

private theorem avoidTwoQuestions_ne_left
    (x y : FourByThreeQuestion) :
    avoidTwoQuestions x y ≠ x :=
  (Classical.choose_spec (exists_question_ne_two x y)).1

private theorem avoidTwoQuestions_ne_right
    (x y : FourByThreeQuestion) :
    avoidTwoQuestions x y ≠ y :=
  (Classical.choose_spec (exists_question_ne_two x y)).2

/--
Change every coordinate in `coordinates` to the ternary value different from
both the center and a reference point.
-/
private noncomputable def oppositeFiberPoint
    (center reference : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer) :
    FourByThreeClause :=
  fun coordinate =>
    if _hcoordinate : coordinate ∈ coordinates then
      avoidTwoQuestions (center coordinate) (reference coordinate)
    else center coordinate

private theorem hammingSupport_oppositeFiberPoint_center
    (center reference : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer) :
    hammingSupport center
      (oppositeFiberPoint center reference coordinates) = coordinates := by
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingSupport, oppositeFiberPoint, hcoordinate,
      Ne.symm (avoidTwoQuestions_ne_left
        (center coordinate) (reference coordinate))]
  · simp [hammingSupport, oppositeFiberPoint, hcoordinate]

private theorem hammingSupport_oppositeFiberPoint_reference
    (center reference : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer)
    (hreference :
      hammingSupport center reference = coordinates) :
    hammingSupport reference
      (oppositeFiberPoint center reference coordinates) = coordinates := by
  ext coordinate
  by_cases hcoordinate : coordinate ∈ coordinates
  · simp [hammingSupport, oppositeFiberPoint, hcoordinate,
      Ne.symm (avoidTwoQuestions_ne_right
        (center coordinate) (reference coordinate))]
  · have hnot :
        coordinate ∉ hammingSupport center reference := by
      rw [hreference]
      exact hcoordinate
    have heq : center coordinate = reference coordinate := by
      simpa [hammingSupport] using hnot
    simp [hammingSupport, oppositeFiberPoint, hcoordinate, heq]

private theorem hammingDistance_oppositeFiberPoint_reference
    (center reference : FourByThreeClause)
    (coordinates : Finset FourByThreePlayer)
    (hreference :
      hammingSupport center reference = coordinates) :
    hammingDistance reference
        (oppositeFiberPoint center reference coordinates) =
      coordinates.card := by
  rw [← hammingSupport_card,
    hammingSupport_oppositeFiberPoint_reference
      center reference coordinates hreference]

/--
Two layer-two points at Hamming distance at most one have the same changed
coordinate support.
-/
theorem hammingSupport_eq_of_layerTwo_neighbor
    (center clause point : FourByThreeClause)
    (hclause : hammingDistance center clause = 2)
    (hpoint : hammingDistance center point = 2)
    (hneighbor : hammingDistance clause point ≤ 1) :
    hammingSupport center clause = hammingSupport center point := by
  let clauseSupport := hammingSupport center clause
  let pointSupport := hammingSupport center point
  let differenceSupport := hammingSupport clause point
  have hclauseCard : clauseSupport.card = 2 := by
    simpa [clauseSupport] using hclause
  have hpointCard : pointSupport.card = 2 := by
    simpa [pointSupport] using hpoint
  have hdifferenceCard : differenceSupport.card ≤ 1 := by
    simpa [differenceSupport] using hneighbor
  by_contra hne
  have hnotClauseSubset : ¬clauseSupport ⊆ pointSupport := by
    intro hsubset
    have heq : clauseSupport = pointSupport := by
      apply Finset.eq_of_subset_of_card_le hsubset
      omega
    exact hne heq
  have hnotPointSubset : ¬pointSupport ⊆ clauseSupport := by
    intro hsubset
    have heq : pointSupport = clauseSupport := by
      apply Finset.eq_of_subset_of_card_le hsubset
      omega
    exact hne heq.symm
  obtain ⟨i, hiClause, hiPoint⟩ :=
    Set.not_subset.mp hnotClauseSubset
  obtain ⟨j, hjPoint, hjClause⟩ :=
    Set.not_subset.mp hnotPointSubset
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hjClause hiClause
  have hiDifference : i ∈ differenceSupport := by
    have hcenterClause : center i ≠ clause i := by
      simpa [clauseSupport, hammingSupport] using hiClause
    have hcenterPoint : center i = point i := by
      simpa [pointSupport, hammingSupport] using hiPoint
    simp only [differenceSupport, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro hclausePoint
    exact hcenterClause (hcenterPoint.trans hclausePoint.symm)
  have hjDifference : j ∈ differenceSupport := by
    have hcenterPoint : center j ≠ point j := by
      simpa [pointSupport, hammingSupport] using hjPoint
    have hcenterClause : center j = clause j := by
      simpa [clauseSupport, hammingSupport] using hjClause
    simp only [differenceSupport, hammingSupport, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro hclausePoint
    exact hcenterPoint (hcenterClause.trans hclausePoint)
  have hpairSubset : ({i, j} : Finset FourByThreePlayer) ⊆ differenceSupport := by
    intro coordinate hcoordinate
    rcases Finset.mem_insert.mp hcoordinate with rfl | hcoordinate
    · exact hiDifference
    · have heq : coordinate = j := by simpa using hcoordinate
      subst coordinate
      exact hjDifference
  have hpairCard : ({i, j} : Finset FourByThreePlayer).card = 2 := by
    simp [hij]
  have hcard := Finset.card_le_card hpairSubset
  omega

/--
If a safe center is unique and every support clause is in layer two or four,
then each two-coordinate support needs at least two layer-two clauses.
-/
theorem sameCoordinateSupportClauses_card_two_le
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hunique : safeCenters support = {center})
    (hlayers :
      ∀ clause ∈ support,
        hammingDistance center clause = 2 ∨
          hammingDistance center clause = 4)
    (coordinates : Finset FourByThreePlayer)
    (hcoordinates : coordinates ∈ coordinateSupportIndices) :
    2 ≤
      (sameCoordinateSupportClauses
        support center coordinates).card := by
  classical
  let fiber :=
    sameCoordinateSupportClauses support center coordinates
  change 2 ≤ fiber.card
  have hcoordinatesCard : coordinates.card = 2 := by
    exact (Finset.mem_powersetCard.mp hcoordinates).2
  have hcovered :
      ∀ point : FourByThreeClause,
        hammingSupport center point = coordinates →
          ∃ clause ∈ fiber, hammingDistance point clause ≤ 1 := by
    intro point hpointSupport
    have hpointLayer :
        hammingDistance center point = 2 := by
      rw [← hammingSupport_card, hpointSupport, hcoordinatesCard]
    have hpointNotSafe : point ∉ safeCenters support := by
      intro hpointSafe
      have hpointCenter : point = center := by
        have : point ∈ ({center} : Finset FourByThreeClause) := by
          rw [← hunique]
          exact hpointSafe
        simpa using this
      subst point
      simp at hpointLayer
    have hnotAll :
        ¬ ∀ clause ∈ support,
            2 ≤ hammingDistance point clause := by
      simpa [safeCenters] using hpointNotSafe
    push Not at hnotAll
    obtain ⟨clause, hclauseSupport, hclauseNear⟩ := hnotAll
    have hnear : hammingDistance point clause ≤ 1 := by omega
    have hclauseLayerTwo :
        hammingDistance center clause = 2 := by
      rcases hlayers clause hclauseSupport with htwo | hfour
      · exact htwo
      · have htriangle :=
          hammingDistance_triangle center point clause
        omega
    have hsameSupport :
        hammingSupport center clause = coordinates := by
      calc
        hammingSupport center clause =
            hammingSupport center point :=
          hammingSupport_eq_of_layerTwo_neighbor
            center clause point hclauseLayerTwo hpointLayer
              (by
                rw [hammingDistance_comm]
                exact hnear)
        _ = coordinates := hpointSupport
    refine ⟨clause, ?_, hnear⟩
    exact Finset.mem_filter.mpr ⟨hclauseSupport, hsameSupport⟩
  by_contra hnotTwo
  have hcard : fiber.card ≤ 1 := by omega
  by_cases hnonempty : fiber.Nonempty
  · let reference : FourByThreeClause := Classical.choose hnonempty
    have hreferenceMem : reference ∈ fiber :=
      Classical.choose_spec hnonempty
    have hreferenceSupport :
        hammingSupport center reference = coordinates :=
      (Finset.mem_filter.mp hreferenceMem).2
    let point :=
      oppositeFiberPoint center reference coordinates
    have hpointSupport :
        hammingSupport center point = coordinates := by
      exact hammingSupport_oppositeFiberPoint_center
        center reference coordinates
    obtain ⟨clause, hclauseMem, hnear⟩ :=
      hcovered point hpointSupport
    have hreferenceClause : reference = clause :=
      (Finset.card_le_one.mp hcard)
        reference hreferenceMem clause hclauseMem
    have hfar :
        hammingDistance reference point = 2 := by
      rw [hammingDistance_oppositeFiberPoint_reference
        center reference coordinates hreferenceSupport,
        hcoordinatesCard]
    rw [← hreferenceClause, hammingDistance_comm] at hnear
    omega
  · let point :=
      oppositeFiberPoint center center coordinates
    have hpointSupport :
        hammingSupport center point = coordinates := by
      exact hammingSupport_oppositeFiberPoint_center
        center center coordinates
    obtain ⟨clause, hclauseMem, _hnear⟩ :=
      hcovered point hpointSupport
    exact hnonempty ⟨clause, hclauseMem⟩

/--
The six coordinate-support fibers partition the layer-two support clauses.
-/
theorem sum_sameCoordinateSupportClauses_card
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause) :
    (∑ coordinates ∈ coordinateSupportIndices,
        (sameCoordinateSupportClauses
          support center coordinates).card) =
      layerTwoClauseCount support center := by
  classical
  let layerTwoClauses :=
    support.filter fun clause =>
      hammingDistance center clause = 2
  have hmaps :
      Set.MapsTo (hammingSupport center)
        layerTwoClauses coordinateSupportIndices := by
    intro clause hclause
    have hlayer :
        hammingDistance center clause = 2 :=
      (Finset.mem_filter.mp hclause).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · exact Finset.subset_univ _
    · simpa [coordinateSupportIndices, hammingSupport_card] using hlayer
  have hpartition :=
    Finset.card_eq_sum_card_fiberwise hmaps
  calc
    (∑ coordinates ∈ coordinateSupportIndices,
        (sameCoordinateSupportClauses
          support center coordinates).card) =
        ∑ coordinates ∈ coordinateSupportIndices,
          (layerTwoClauses.filter fun clause =>
            hammingSupport center clause = coordinates).card := by
      apply Finset.sum_congr rfl
      intro coordinates hcoordinates
      have hcoordinatesCard : coordinates.card = 2 :=
        (Finset.mem_powersetCard.mp hcoordinates).2
      congr 1
      ext clause
      simp only [layerTwoClauses, sameCoordinateSupportClauses,
        Finset.mem_filter, and_congr_left_iff]
      intro hsupport
      constructor
      · intro hclause
        refine ⟨hclause, ?_⟩
        rw [← hammingSupport_card, hsupport, hcoordinatesCard]
      · exact And.left
    _ = layerTwoClauses.card := hpartition.symm
    _ = layerTwoClauseCount support center := rfl

/--
A center whose support clauses all lie in layers two and four forces the
tradeoff `25 ≤ 3 a + |U|`, where `a` is its layer-two clause count and `U`
is the global safe-center set.
-/
theorem layerTwo_safeCenters_tradeoff
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hlayers :
      ∀ clause ∈ support,
        hammingDistance center clause = 2 ∨
          hammingDistance center clause = 4) :
    25 ≤
      3 * layerTwoClauseCount support center +
        (safeCenters support).card := by
  classical
  let layerTwoClauses :=
    support.filter fun clause =>
      hammingDistance center clause = 2
  let layerTwoSphere := hammingSphere center 2
  let safeLayerTwo := layerTwoSphere ∩ safeCenters support
  let unsafeLayerTwo := layerTwoSphere \ safeCenters support
  let coveredByLayerTwo :=
    layerTwoClauses.biUnion fun clause =>
      radiusOneBall clause ∩ layerTwoSphere
  have hcoveredCard :
      coveredByLayerTwo.card ≤ 3 * layerTwoClauses.card := by
    have hcover :=
      Finset.card_biUnion_le_card_mul layerTwoClauses
        (fun clause => radiusOneBall clause ∩ layerTwoSphere) 3
        (fun clause hclause =>
          layerTwo_ball_slice_card_le_three center clause
            (Finset.mem_filter.mp hclause).2)
    simpa [coveredByLayerTwo, layerTwoSphere, Nat.mul_comm] using hcover
  have hunsafeSubset : unsafeLayerTwo ⊆ coveredByLayerTwo := by
    intro point hpoint
    have hpointSphere : point ∈ layerTwoSphere :=
      (Finset.mem_sdiff.mp hpoint).1
    have hpointDistance :
        hammingDistance center point = 2 := by
      simpa [layerTwoSphere, hammingSphere] using hpointSphere
    have hpointNotSafe : point ∉ safeCenters support :=
      (Finset.mem_sdiff.mp hpoint).2
    have hnotAll :
        ¬ ∀ clause ∈ support,
            2 ≤ hammingDistance point clause := by
      simpa [safeCenters] using hpointNotSafe
    push Not at hnotAll
    obtain ⟨clause, hclauseSupport, hclauseNear⟩ := hnotAll
    have hclauseNear' : hammingDistance point clause ≤ 1 := by
      omega
    have hclauseLayerTwo :
        hammingDistance center clause = 2 := by
      rcases hlayers clause hclauseSupport with htwo | hfour
      · exact htwo
      · have htriangle :=
          hammingDistance_triangle center point clause
        omega
    apply Finset.mem_biUnion.mpr
    refine ⟨clause, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨hclauseSupport, hclauseLayerTwo⟩
    · apply Finset.mem_inter.mpr
      constructor
      · simp only [radiusOneBall, closedHammingBall,
          Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hammingDistance_comm]
        exact hclauseNear'
      · exact hpointSphere
  have hunsafeCard :
      unsafeLayerTwo.card ≤ 3 * layerTwoClauses.card :=
    (Finset.card_le_card hunsafeSubset).trans hcoveredCard
  have hsphereCard : layerTwoSphere.card = 24 := by
    simp [layerTwoSphere]
  have hpartitionCard :=
    Finset.card_sdiff_add_card_inter
      layerTwoSphere (safeCenters support)
  have hsafeLayerCard :
      24 ≤ 3 * layerTwoClauses.card + safeLayerTwo.card := by
    change
      unsafeLayerTwo.card + safeLayerTwo.card =
        layerTwoSphere.card at hpartitionCard
    omega
  have hcenterSafe : center ∈ safeCenters support := by
    simp only [safeCenters, Finset.mem_filter,
      Finset.mem_univ, true_and]
    intro clause hclause
    rcases hlayers clause hclause with htwo | hfour
    · omega
    · omega
  have hcenterNotSafeLayerTwo : center ∉ safeLayerTwo := by
    intro hcenter
    have hcenterSphere := (Finset.mem_inter.mp hcenter).1
    simp [layerTwoSphere, hammingSphere] at hcenterSphere
  have hinsertSubset :
      insert center safeLayerTwo ⊆ safeCenters support := by
    intro point hpoint
    rcases Finset.mem_insert.mp hpoint with rfl | hpoint
    · exact hcenterSafe
    · exact (Finset.mem_inter.mp hpoint).2
  have hinsertCard :
      (insert center safeLayerTwo).card =
        safeLayerTwo.card + 1 := by
    rw [Finset.card_insert_of_notMem hcenterNotSafeLayerTwo]
  have hinsertLe :
      safeLayerTwo.card + 1 ≤
        (safeCenters support).card := by
    rw [← hinsertCard]
    exact Finset.card_le_card hinsertSubset
  change
    25 ≤ 3 * layerTwoClauses.card +
      (safeCenters support).card
  omega

/--
If there are at most six safe centers, the layer tradeoff forces at least
seven layer-two support clauses about every center satisfying the layer
hypothesis.
-/
theorem safeCenter_layerTwoClauseCount_seven_le
    (support : Finset FourByThreeClause)
    (center : FourByThreeClause)
    (hsafeCard : (safeCenters support).card ≤ 6)
    (hlayers :
      ∀ clause ∈ support,
        hammingDistance center clause = 2 ∨
          hammingDistance center clause = 4) :
    7 ≤ layerTwoClauseCount support center := by
  have htradeoff :=
    layerTwo_safeCenters_tradeoff support center hlayers
  omega

/--
For ten support clauses, the local seven-clause lower bound and the global
coverage-excess inequality force a nonempty family of at most six separated
safe centers to consist of exactly one center.
-/
theorem safeCenters_card_eq_one_of_ten
    (support : Finset FourByThreeClause)
    (hsupportCard : support.card = 10)
    (hsafeNonempty : (safeCenters support).Nonempty)
    (hsafeCard : (safeCenters support).card ≤ 6)
    (hsafeSeparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (hlayers :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          hammingDistance center clause = 2 ∨
            hammingDistance center clause = 4) :
    (safeCenters support).card = 1 := by
  have heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause) := by
    intro center hcenter clause hclause
    rcases hlayers center hcenter clause hclause with htwo | hfour
    · rw [htwo]
      exact ⟨1, rfl⟩
    · rw [hfour]
      exact ⟨2, rfl⟩
  have hexcess :=
    safeHole_neighborhood_excess support hsafeSeparated heven
  have hseven :
      ∀ center ∈ safeCenters support,
        7 ≤ safeHoleLayerTwoCount support center := by
    intro center hcenter
    simpa [layerTwoClauseCount, safeHoleLayerTwoCount] using
      safeCenter_layerTwoClauseCount_seven_le
        support center hsafeCard (hlayers center hcenter)
  have hsumLower :
      (3 : ℤ) * ((safeCenters support).card : ℤ) ≤
        ∑ center ∈ safeCenters support,
          ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
    calc
      (3 : ℤ) * ((safeCenters support).card : ℤ) =
          ∑ _center ∈ safeCenters support, (3 : ℤ) := by
        simp [mul_comm]
      _ ≤
          ∑ center ∈ safeCenters support,
            ((safeHoleLayerTwoCount support center : ℤ) - 4) := by
        apply Finset.sum_le_sum
        intro center hcenter
        have hlower := hseven center hcenter
        omega
  have hcardUpper :
      ((safeCenters support).card : ℤ) ≤ 1 := by
    have hglobal := hexcess.2
    rw [hsupportCard] at hglobal
    nlinarith
  have hcardPositive :
      1 ≤ (safeCenters support).card :=
    Finset.card_pos.mpr hsafeNonempty
  have hcardUpperNat :
      (safeCenters support).card ≤ 1 := by
    exact_mod_cast hcardUpper
  omega

/--
Every full rational circuit on ten distinct clauses has a safe center.

Otherwise the ten radius-one balls cover the whole clause space, contradicting
the connected-Gram obstruction for a full ten-row circuit.
-/
theorem tenClause_fullCircuit_has_safeCenter
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 10)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    ∃ center : FourByThreeClause,
      ∀ e : E, 2 ≤ hammingDistance center (query e) := by
  classical
  by_contra hsafe
  push Not at hsafe
  have hcover :
      RadiusOneBallCover (Finset.univ.image query) := by
    intro point
    obtain ⟨e, hnear⟩ := hsafe point
    rw [ballCoverMultiplicity]
    apply Finset.card_pos.mpr
    refine ⟨query e, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_image.mpr
        ⟨e, Finset.mem_univ e, rfl⟩
    · simp only [radiusOneBall, closedHammingBall,
        Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hammingDistance_comm]
      omega
  exact
    (tenBallCover_not_fullRationalCircuit
      query hquery hcard hcover) hCircuit

/--
The structural ten-clause noncoverage contradiction.

The hypotheses expose the four pieces of hard-center geometry used after
the support-cardinality assumption: safe centers exist, there are at most
six of them, distinct ones are distance at least three apart, and every
support clause is in layer two or four about every safe center.
-/
theorem tenClause_noncovering_geometry_impossible
    (support : Finset FourByThreeClause)
    (hsupportCard : support.card = 10)
    (hsafeNonempty : (safeCenters support).Nonempty)
    (hsafeCard : (safeCenters support).card ≤ 6)
    (hsafeSeparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support → u ≠ v →
          3 ≤ hammingDistance u v)
    (hlayers :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          hammingDistance center clause = 2 ∨
            hammingDistance center clause = 4) :
    False := by
  classical
  have hsafeCardOne :=
    safeCenters_card_eq_one_of_ten support hsupportCard
      hsafeNonempty hsafeCard hsafeSeparated hlayers
  obtain ⟨center, hunique⟩ :=
    Finset.card_eq_one.mp hsafeCardOne
  have hcenterSafe : center ∈ safeCenters support := by
    rw [hunique]
    simp
  have hfiberLower :
      ∀ coordinates ∈ coordinateSupportIndices,
        2 ≤
          (sameCoordinateSupportClauses
            support center coordinates).card := by
    intro coordinates hcoordinates
    exact sameCoordinateSupportClauses_card_two_le
      support center hunique (hlayers center hcenterSafe)
        coordinates hcoordinates
  have hsumLower :
      12 ≤
        ∑ coordinates ∈ coordinateSupportIndices,
          (sameCoordinateSupportClauses
            support center coordinates).card := by
    calc
      12 =
          ∑ _coordinates ∈ coordinateSupportIndices, 2 := by
        simp
      _ ≤
          ∑ coordinates ∈ coordinateSupportIndices,
            (sameCoordinateSupportClauses
              support center coordinates).card := by
        apply Finset.sum_le_sum
        intro coordinates hcoordinates
        exact hfiberLower coordinates hcoordinates
  have hlayerTwoLower :
      12 ≤ layerTwoClauseCount support center := by
    rw [← sum_sameCoordinateSupportClauses_card support center]
    exact hsumLower
  have hlayerTwoUpper :
      layerTwoClauseCount support center ≤ support.card := by
    exact Finset.card_le_card (Finset.filter_subset _ _)
  omega

end

end QIT.XORGame

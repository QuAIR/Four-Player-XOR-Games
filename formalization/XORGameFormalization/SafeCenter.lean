/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Hamming
import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Safe-center combinatorics for four-player ternary XOR games

This module isolates the Hamming-geometric arguments at the nine-clause
structural boundary.  The proofs are uniform finite-set arguments: they do not
invoke the clause-circuit census.
-/

@[expose] public section

namespace QIT
namespace XORGame

open scoped BigOperators

noncomputable section

/-- The coordinates on which `point` differs from `center`. -/
def hammingSupport (center point : FourByThreeClause) : Finset FourByThreePlayer :=
  Finset.univ.filter fun coordinate => center coordinate ≠ point coordinate

@[simp]
theorem hammingSupport_card (center point : FourByThreeClause) :
    (hammingSupport center point).card = hammingDistance center point := rfl

/-- Centers not covered by a radius-one ball about any member of `support`. -/
def safeCenters (support : Finset FourByThreeClause) : Finset FourByThreeClause :=
  Finset.univ.filter fun center =>
    ∀ clause ∈ support, 2 ≤ hammingDistance center clause

/-- The coordinate-value pairs different from a fixed center. -/
private def changedValuePairs (center : FourByThreeClause) :
    Finset (FourByThreePlayer × FourByThreeQuestion) :=
  Finset.univ.filter fun pair => center pair.1 ≠ pair.2

private theorem changedValuePairs_card (center : FourByThreeClause) :
    (changedValuePairs center).card = 8 := by
  let graph : Finset (FourByThreePlayer × FourByThreeQuestion) :=
    Finset.univ.image fun coordinate => (coordinate, center coordinate)
  have hgraph_card : graph.card = 4 := by
    rw [Finset.card_image_of_injective]
    · exact Fintype.card_fin 4
    · intro a b hab
      exact congrArg Prod.fst hab
  have hchanged :
      changedValuePairs center =
        (Finset.univ : Finset (FourByThreePlayer × FourByThreeQuestion)) \ graph := by
    ext ⟨coordinate, question⟩
    simp [changedValuePairs, graph, eq_comm]
  rw [hchanged, Finset.card_sdiff]
  simp [hgraph_card]

/--
If two layer-two words share the same changed value in one coordinate, then
they differ in at most two coordinates.
-/
private theorem hammingDistance_le_two_of_layer_two_shared
    (center x y : FourByThreeClause) (coordinate : FourByThreePlayer)
    (hx : hammingDistance center x = 2)
    (hy : hammingDistance center y = 2)
    (hcx : center coordinate ≠ x coordinate)
    (hcy : center coordinate ≠ y coordinate)
    (hxyCoordinate : x coordinate = y coordinate) :
    hammingDistance x y ≤ 2 := by
  let sx := hammingSupport center x
  let sy := hammingSupport center y
  let differences := hammingSupport x y
  have hsx_card : sx.card = 2 := by
    simpa [sx] using hx
  have hsy_card : sy.card = 2 := by
    simpa [sy] using hy
  have hcoordinate_inter : coordinate ∈ sx ∩ sy := by
    exact Finset.mem_inter.mpr ⟨
      (by simpa [sx, hammingSupport] using hcx),
      (by simpa [sy, hammingSupport] using hcy)⟩
  have hinter_card : 1 ≤ (sx ∩ sy).card :=
    Finset.one_le_card.mpr ⟨coordinate, hcoordinate_inter⟩
  have hunion_card : (sx ∪ sy).card ≤ 3 := by
    have hcard := Finset.card_union_add_card_inter sx sy
    omega
  have hcoordinate_union : coordinate ∈ sx ∪ sy :=
    Finset.mem_union_left sy (Finset.mem_inter.mp hcoordinate_inter).1
  have herase_card : ((sx ∪ sy).erase coordinate).card ≤ 2 := by
    rw [Finset.card_erase_of_mem hcoordinate_union]
    omega
  have hdifferences_subset : differences ⊆ (sx ∪ sy).erase coordinate := by
    intro i hi
    have hixy : x i ≠ y i := by
      simpa [differences, hammingSupport] using hi
    have hiunion : i ∈ sx ∪ sy := by
      by_contra hi
      simp only [Finset.mem_union, not_or] at hi
      have hcx' : center i = x i := by
        simpa [sx, hammingSupport] using hi.1
      have hcy' : center i = y i := by
        simpa [sy, hammingSupport] using hi.2
      exact hixy (hcx'.symm.trans hcy')
    have hine : i ≠ coordinate := by
      intro hieq
      subst i
      exact hixy hxyCoordinate
    exact Finset.mem_erase.mpr ⟨hine, hiunion⟩
  calc
    hammingDistance x y = differences.card := rfl
    _ ≤ ((sx ∪ sy).erase coordinate).card :=
      Finset.card_le_card hdifferences_subset
    _ ≤ 2 := herase_card

/--
A pairwise distance-three family in Hamming layer two has at most four
members.  The proof injects its two incidences per word into the eight
possible changed coordinate-value pairs.
-/
theorem separated_layer_two_card_le_four
    (center : FourByThreeClause) (family : Finset FourByThreeClause)
    (hlayer : ∀ point ∈ family, hammingDistance center point = 2)
    (hseparated :
      ∀ ⦃x⦄, x ∈ family → ∀ ⦃y⦄, y ∈ family → x ≠ y →
        3 ≤ hammingDistance x y) :
    family.card ≤ 4 := by
  let incidences :=
    family.sigma fun point => hammingSupport center point
  have hincidences_card : incidences.card = 2 * family.card := by
    rw [Finset.card_sigma]
    calc
      ∑ point ∈ family, (hammingSupport center point).card =
          ∑ _point ∈ family, 2 := by
        apply Finset.sum_congr rfl
        intro point hpoint
        simp [hlayer point hpoint]
      _ = 2 * family.card := by simp [Nat.mul_comm]
  let recordValue :
      (Σ _point : FourByThreeClause, FourByThreePlayer) →
        FourByThreePlayer × FourByThreeQuestion :=
    fun incidence => (incidence.2, incidence.1 incidence.2)
  have hmaps :
      Set.MapsTo recordValue incidences (changedValuePairs center) := by
    rintro ⟨point, coordinate⟩ hmem
    have hcoordinate :=
      (Finset.mem_sigma.mp hmem).2
    simpa [recordValue, changedValuePairs, hammingSupport] using hcoordinate
  have hinjective : (incidences : Set _).InjOn recordValue := by
    rintro ⟨x, a⟩ hx ⟨y, b⟩ hy heq
    have hxa := Finset.mem_sigma.mp hx
    have hyb := Finset.mem_sigma.mp hy
    have hxFamily : x ∈ family := hxa.1
    have hyFamily : y ∈ family := hyb.1
    have hab : a = b := congrArg Prod.fst heq
    subst b
    have hvalue : x a = y a := congrArg Prod.snd heq
    have hxy : x = y := by
      by_contra hne
      have hlower : 3 ≤ hammingDistance x y :=
        hseparated hxFamily hyFamily hne
      have hupper := hammingDistance_le_two_of_layer_two_shared
        center x y a (hlayer x hxFamily) (hlayer y hyFamily)
        (by simpa [hammingSupport] using hxa.2)
        (by simpa [hammingSupport] using hyb.2) hvalue
      omega
    subst y
    rfl
  have hcard_le :
      incidences.card ≤ (changedValuePairs center).card :=
    Finset.card_le_card_of_injOn recordValue hmaps hinjective
  rw [hincidences_card, changedValuePairs_card] at hcard_le
  omega

private theorem ternary_eq_left_or_eq_right
    (center x y z : FourByThreeQuestion)
    (hx : x ≠ center) (hy : y ≠ center) (hz : z ≠ center)
    (hyz : y ≠ z) :
    x = y ∨ x = z := by
  have htriple_card :
      ({center, y, z} : Finset FourByThreeQuestion).card = 3 := by
    rw [Finset.card_triple_eq_three_iff]
    exact ⟨Ne.symm hy, Ne.symm hz, hyz⟩
  have htriple :
      ({center, y, z} : Finset FourByThreeQuestion) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [htriple_card]
  have hxmem : x ∈ ({center, y, z} : Finset FourByThreeQuestion) := by
    rw [htriple]
    exact Finset.mem_univ x
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxmem
  rcases hxmem with hxc | hxy | hxz
  · exact False.elim (hx hxc)
  · exact Or.inl hxy
  · exact Or.inr hxz

private theorem hammingSupport_eq_univ_of_distance_four
    (center point : FourByThreeClause)
    (h : hammingDistance center point = 4) :
    hammingSupport center point = Finset.univ := by
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simp [hammingSupport_card, h]

/--
A pairwise distance-three family in Hamming layer four has at most two
members.
-/
theorem separated_layer_four_card_le_two
    (center : FourByThreeClause) (family : Finset FourByThreeClause)
    (hlayer : ∀ point ∈ family, hammingDistance center point = 4)
    (hseparated :
      ∀ ⦃x⦄, x ∈ family → ∀ ⦃y⦄, y ∈ family → x ≠ y →
        3 ≤ hammingDistance x y) :
    family.card ≤ 2 := by
  by_contra hcard
  have hthree : 2 < family.card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card.mp hthree
  let a := hammingSupport x y
  let b := hammingSupport x z
  have ha_lower : 3 ≤ a.card := by
    simpa [a] using hseparated hx hy hxy
  have hb_lower : 3 ≤ b.card := by
    simpa [b] using hseparated hx hz hxz
  have huniv_card :
      (Finset.univ : Finset FourByThreePlayer).card = 4 := by
    exact Fintype.card_fin 4
  have ha_compl : ((Finset.univ : Finset FourByThreePlayer) \ a).card ≤ 1 := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ]
    omega
  have hb_compl : ((Finset.univ : Finset FourByThreePlayer) \ b).card ≤ 1 := by
    rw [Finset.card_sdiff]
    simp only [Finset.inter_univ]
    omega
  have hx_layer := hammingSupport_eq_univ_of_distance_four center x (hlayer x hx)
  have hy_layer := hammingSupport_eq_univ_of_distance_four center y (hlayer y hy)
  have hz_layer := hammingSupport_eq_univ_of_distance_four center z (hlayer z hz)
  have hyz_subset :
      hammingSupport y z ⊆
        ((Finset.univ : Finset FourByThreePlayer) \ a) ∪
          (Finset.univ \ b) := by
    intro coordinate hcoordinate
    have hyzValue : y coordinate ≠ z coordinate := by
      simpa [hammingSupport] using hcoordinate
    have hcx : x coordinate ≠ center coordinate := by
      have : coordinate ∈ hammingSupport center x := by
        rw [hx_layer]
        exact Finset.mem_univ coordinate
      exact Ne.symm (by simpa [hammingSupport] using this)
    have hcy : y coordinate ≠ center coordinate := by
      have : coordinate ∈ hammingSupport center y := by
        rw [hy_layer]
        exact Finset.mem_univ coordinate
      exact Ne.symm (by simpa [hammingSupport] using this)
    have hcz : z coordinate ≠ center coordinate := by
      have : coordinate ∈ hammingSupport center z := by
        rw [hz_layer]
        exact Finset.mem_univ coordinate
      exact Ne.symm (by simpa [hammingSupport] using this)
    rcases ternary_eq_left_or_eq_right
        (center coordinate) (x coordinate) (y coordinate) (z coordinate)
        hcx hcy hcz hyzValue with hsameXY | hsameXZ
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ coordinate, by
        simpa [a, hammingSupport] using hsameXY⟩
    · apply Finset.mem_union_right
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ coordinate, by
        simpa [b, hammingSupport] using hsameXZ⟩
  have hyz_upper : hammingDistance y z ≤ 2 := by
    calc
      hammingDistance y z = (hammingSupport y z).card := rfl
      _ ≤
          (((Finset.univ : Finset FourByThreePlayer) \ a) ∪
            (Finset.univ \ b)).card :=
        Finset.card_le_card hyz_subset
      _ ≤
          ((Finset.univ : Finset FourByThreePlayer) \ a).card +
            ((Finset.univ : Finset FourByThreePlayer) \ b).card :=
        Finset.card_union_le _ _
      _ ≤ 2 := by omega
  have hyz_lower := hseparated hy hz hyz
  omega

/--
A separated family lying in the union of layers two and four has at most six
members.
-/
theorem separated_layers_two_four_card_le_six
    (center : FourByThreeClause) (family : Finset FourByThreeClause)
    (hlayers :
      ∀ point ∈ family,
        hammingDistance center point = 2 ∨
          hammingDistance center point = 4)
    (hseparated :
      ∀ ⦃x⦄, x ∈ family → ∀ ⦃y⦄, y ∈ family → x ≠ y →
        3 ≤ hammingDistance x y) :
    family.card ≤ 6 := by
  let layerTwo :=
    family.filter fun point => hammingDistance center point = 2
  let layerFour :=
    family.filter fun point => hammingDistance center point = 4
  have hpartition : family = layerTwo ∪ layerFour := by
    ext point
    simp only [layerTwo, layerFour, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hpoint
      rcases hlayers point hpoint with htwo | hfour
      · exact Or.inl ⟨hpoint, htwo⟩
      · exact Or.inr ⟨hpoint, hfour⟩
    · rintro (⟨hpoint, -⟩ | ⟨hpoint, -⟩) <;> exact hpoint
  have htwo : layerTwo.card ≤ 4 := by
    apply separated_layer_two_card_le_four center layerTwo
    · intro point hpoint
      exact (Finset.mem_filter.mp hpoint).2
    · intro x hx y hy hxy
      exact hseparated (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1 hxy
  have hfour : layerFour.card ≤ 2 := by
    apply separated_layer_four_card_le_two center layerFour
    · intro point hpoint
      exact (Finset.mem_filter.mp hpoint).2
    · intro x hx y hy hxy
      exact hseparated (Finset.mem_filter.mp hx).1
        (Finset.mem_filter.mp hy).1 hxy
  rw [hpartition]
  exact
    (Finset.card_union_le layerTwo layerFour).trans
      (Nat.add_le_add htwo hfour)

private theorem neighborDifference_subset_layerSupport
    (center clause point : FourByThreeClause)
    (hclause : hammingDistance center clause = 2)
    (hpoint : hammingDistance center point = 2)
    (hneighbor : hammingDistance clause point ≤ 1) :
    hammingSupport clause point ⊆ hammingSupport center clause := by
  let clauseSupport := hammingSupport center clause
  let pointSupport := hammingSupport center point
  let differenceSupport := hammingSupport clause point
  have hclauseCard : clauseSupport.card = 2 := by
    simpa [clauseSupport] using hclause
  have hpointCard : pointSupport.card = 2 := by
    simpa [pointSupport] using hpoint
  have hdifferenceCard : differenceSupport.card ≤ 1 := by
    simpa [differenceSupport] using hneighbor
  have hdifferenceSubsingleton :
      ∀ a ∈ differenceSupport, ∀ b ∈ differenceSupport, a = b :=
    Finset.card_le_one.mp hdifferenceCard
  intro coordinate hcoordinate
  by_contra hcoordinateClause
  have hcenterClause :
      center coordinate = clause coordinate := by
    simpa [clauseSupport, hammingSupport] using hcoordinateClause
  have hcoordinatePoint : coordinate ∈ pointSupport := by
    have hclausePoint : clause coordinate ≠ point coordinate := by
      simpa [differenceSupport, hammingSupport] using hcoordinate
    simpa [pointSupport, hammingSupport, hcenterClause] using hclausePoint
  have hclauseSubsetPoint : clauseSupport ⊆ pointSupport := by
    intro other hotherClause
    by_contra hotherPoint
    have hcenterClauseOther :
        center other ≠ clause other := by
      simpa [clauseSupport, hammingSupport] using hotherClause
    have hcenterPointOther :
        center other = point other := by
      simpa [pointSupport, hammingSupport] using hotherPoint
    have hotherDifference : other ∈ differenceSupport := by
      simp only [differenceSupport, hammingSupport, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact fun h =>
        hcenterClauseOther (hcenterPointOther.trans h.symm)
    have heq :=
      hdifferenceSubsingleton coordinate hcoordinate other hotherDifference
    subst other
    exact hcoordinateClause hotherClause
  have hinsertSubset :
      insert coordinate clauseSupport ⊆ pointSupport := by
    intro other hother
    rcases Finset.mem_insert.mp hother with rfl | hother
    · exact hcoordinatePoint
    · exact hclauseSubsetPoint hother
  have hinsertCard : (insert coordinate clauseSupport).card = 3 := by
    rw [Finset.card_insert_of_notMem hcoordinateClause, hclauseCard]
  have hcard :=
    Finset.card_le_card hinsertSubset
  omega

private theorem layerTwo_neighbor_changed_coordinate_stays_changed
    (center clause point : FourByThreeClause)
    (hclause : hammingDistance center clause = 2)
    (hpoint : hammingDistance center point = 2)
    (hneighbor : hammingDistance clause point ≤ 1)
    ⦃coordinate : FourByThreePlayer⦄
    (hcoordinate : coordinate ∈ hammingSupport clause point) :
    coordinate ∈ hammingSupport center point := by
  let clauseSupport := hammingSupport center clause
  let pointSupport := hammingSupport center point
  let differenceSupport := hammingSupport clause point
  have hclauseCard : clauseSupport.card = 2 := by
    simpa [clauseSupport] using hclause
  have hpointCard : pointSupport.card = 2 := by
    simpa [pointSupport] using hpoint
  have hdifferenceCard : differenceSupport.card ≤ 1 := by
    simpa [differenceSupport] using hneighbor
  have hdifferenceSubsingleton :
      ∀ a ∈ differenceSupport, ∀ b ∈ differenceSupport, a = b :=
    Finset.card_le_one.mp hdifferenceCard
  have hcoordinateDifference : coordinate ∈ differenceSupport := by
    exact hcoordinate
  have hcoordinateClause : coordinate ∈ clauseSupport :=
    neighborDifference_subset_layerSupport center clause point
      hclause hpoint hneighbor hcoordinate
  by_contra hcoordinatePoint
  have hpointSubset :
      pointSupport ⊆ clauseSupport.erase coordinate := by
    intro other hotherPoint
    have hotherNe : other ≠ coordinate := by
      intro heq
      subst other
      exact hcoordinatePoint hotherPoint
    have hotherClause : other ∈ clauseSupport := by
      by_contra hotherClause
      have hcenterClauseOther :
          center other = clause other := by
        simpa [clauseSupport, hammingSupport] using hotherClause
      have hcenterPointOther :
          center other ≠ point other := by
        simpa [pointSupport, hammingSupport] using hotherPoint
      have hotherDifference : other ∈ differenceSupport := by
        simp only [differenceSupport, hammingSupport, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact fun h =>
          hcenterPointOther (hcenterClauseOther.trans h)
      have heq :=
        hdifferenceSubsingleton coordinate hcoordinateDifference
          other hotherDifference
      exact hotherNe heq.symm
    exact Finset.mem_erase.mpr ⟨hotherNe, hotherClause⟩
  have heraseCard : (clauseSupport.erase coordinate).card = 1 := by
    rw [Finset.card_erase_of_mem hcoordinateClause, hclauseCard]
  have hcard := Finset.card_le_card hpointSubset
  omega

/-- The part of a clause's radius-one ball lying in layer two about `center`. -/
private def layerTwoBallSlice
    (center clause : FourByThreeClause) : Finset FourByThreeClause :=
  radiusOneBall clause ∩ hammingSphere center 2

private def subsetsOfCardAtMostOne
    (coordinates : Finset FourByThreePlayer) :
    Finset (Finset FourByThreePlayer) :=
  coordinates.powerset.filter fun subset => subset.card ≤ 1

private theorem subsetsOfCardAtMostOne_card_le_three
    (coordinates : Finset FourByThreePlayer)
    (hcoordinates : coordinates.card = 2) :
    (subsetsOfCardAtMostOne coordinates).card ≤ 3 := by
  have hsubset :
      subsetsOfCardAtMostOne coordinates ⊆
        coordinates.powersetCard 0 ∪ coordinates.powersetCard 1 := by
    intro subset hsubset
    have hdata := Finset.mem_filter.mp hsubset
    have hsmall : subset.card = 0 ∨ subset.card = 1 := by omega
    rcases hsmall with hzero | hone
    · exact Finset.mem_union_left _ <|
        Finset.mem_powersetCard.mpr ⟨
          Finset.mem_powerset.mp hdata.1, hzero⟩
    · exact Finset.mem_union_right _ <|
        Finset.mem_powersetCard.mpr ⟨
          Finset.mem_powerset.mp hdata.1, hone⟩
  calc
    (subsetsOfCardAtMostOne coordinates).card ≤
        (coordinates.powersetCard 0 ∪ coordinates.powersetCard 1).card :=
      Finset.card_le_card hsubset
    _ ≤
        (coordinates.powersetCard 0).card +
          (coordinates.powersetCard 1).card :=
      Finset.card_union_le _ _
    _ = 3 := by
      simp [Finset.card_powersetCard, hcoordinates]

private theorem layerTwoBallSlice_support_injective
    (center clause : FourByThreeClause)
    (hclause : hammingDistance center clause = 2) :
    (layerTwoBallSlice center clause : Set FourByThreeClause).InjOn
      (hammingSupport clause) := by
  intro x hx y hy hequal
  have hxmem := Finset.mem_inter.mp hx
  have hymem := Finset.mem_inter.mp hy
  have hxneighbor : hammingDistance clause x ≤ 1 := by
    simpa [layerTwoBallSlice, radiusOneBall, closedHammingBall] using hxmem.1
  have hyneighbor : hammingDistance clause y ≤ 1 := by
    simpa [layerTwoBallSlice, radiusOneBall, closedHammingBall] using hymem.1
  have hxlayer : hammingDistance center x = 2 := by
    simpa [layerTwoBallSlice, hammingSphere] using hxmem.2
  have hylayer : hammingDistance center y = 2 := by
    simpa [layerTwoBallSlice, hammingSphere] using hymem.2
  apply funext
  intro coordinate
  by_cases hcoordinate : coordinate ∈ hammingSupport clause x
  · have hcoordinateY : coordinate ∈ hammingSupport clause y := by
      rw [← hequal]
      exact hcoordinate
    have hclauseX : clause coordinate ≠ x coordinate := by
      simpa [hammingSupport] using hcoordinate
    have hclauseY : clause coordinate ≠ y coordinate := by
      simpa [hammingSupport] using hcoordinateY
    have hcenterClause : clause coordinate ≠ center coordinate := by
      have hsubset :=
        neighborDifference_subset_layerSupport center clause x
          hclause hxlayer hxneighbor hcoordinate
      exact Ne.symm (by simpa [hammingSupport] using hsubset)
    have hcenterX : x coordinate ≠ center coordinate := by
      have hchanged :=
        layerTwo_neighbor_changed_coordinate_stays_changed
          center clause x hclause hxlayer hxneighbor hcoordinate
      exact Ne.symm (by simpa [hammingSupport] using hchanged)
    have hcenterY : y coordinate ≠ center coordinate := by
      have hchanged :=
        layerTwo_neighbor_changed_coordinate_stays_changed
          center clause y hclause hylayer hyneighbor hcoordinateY
      exact Ne.symm (by simpa [hammingSupport] using hchanged)
    rcases ternary_eq_left_or_eq_right
        (center coordinate) (x coordinate) (clause coordinate) (y coordinate)
        hcenterX hcenterClause hcenterY hclauseY with hxc | hxy
    · exact False.elim (hclauseX hxc.symm)
    · exact hxy
  · have hcoordinateY : coordinate ∉ hammingSupport clause y := by
      rw [← hequal]
      exact hcoordinate
    have hclauseX : clause coordinate = x coordinate := by
      simpa [hammingSupport] using hcoordinate
    have hclauseY : clause coordinate = y coordinate := by
      simpa [hammingSupport] using hcoordinateY
    exact hclauseX.symm.trans hclauseY

/--
If `clause` is in layer two about `center`, its radius-one ball contains at
most three layer-two points about `center`.
-/
theorem layerTwo_ball_slice_card_le_three
    (center clause : FourByThreeClause)
    (hclause : hammingDistance center clause = 2) :
    (radiusOneBall clause ∩ hammingSphere center 2).card ≤ 3 := by
  let slice := layerTwoBallSlice center clause
  let candidates :=
    subsetsOfCardAtMostOne (hammingSupport center clause)
  have hmaps :
      Set.MapsTo (hammingSupport clause) slice candidates := by
    intro point hpoint
    have hmem := Finset.mem_inter.mp hpoint
    have hneighbor : hammingDistance clause point ≤ 1 := by
      simpa [slice, layerTwoBallSlice, radiusOneBall, closedHammingBall]
        using hmem.1
    have hpointLayer : hammingDistance center point = 2 := by
      simpa [slice, layerTwoBallSlice, hammingSphere] using hmem.2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_powerset.mpr <|
        neighborDifference_subset_layerSupport center clause point
          hclause hpointLayer hneighbor
    · simpa using hneighbor
  have hcard :
      slice.card ≤ candidates.card :=
    Finset.card_le_card_of_injOn (hammingSupport clause) hmaps <|
      layerTwoBallSlice_support_injective center clause hclause
  have hcandidates :
      candidates.card ≤ 3 :=
    subsetsOfCardAtMostOne_card_le_three
      (hammingSupport center clause) (by simpa using hclause)
  exact hcard.trans hcandidates

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

/-- A deterministic third ternary value, different from both inputs. -/
private noncomputable def thirdQuestion
    (x y : FourByThreeQuestion) : FourByThreeQuestion :=
  Classical.choose (exists_question_ne_two x y)

private theorem thirdQuestion_ne_left
    (x y : FourByThreeQuestion) :
    thirdQuestion x y ≠ x :=
  (Classical.choose_spec (exists_question_ne_two x y)).1

private theorem thirdQuestion_ne_right
    (x y : FourByThreeQuestion) :
    thirdQuestion x y ≠ y :=
  (Classical.choose_spec (exists_question_ne_two x y)).2

/--
Change one coordinate of `clause` to the third ternary value relative to the
center and the old clause value.
-/
private noncomputable def flipToThird
    (center clause : FourByThreeClause)
    (coordinate : FourByThreePlayer) : FourByThreeClause :=
  Function.update clause coordinate
    (thirdQuestion (center coordinate) (clause coordinate))

private theorem hammingSupport_flipToThird
    (center clause : FourByThreeClause)
    (coordinate : FourByThreePlayer) :
    hammingSupport clause (flipToThird center clause coordinate) =
      {coordinate} := by
  ext other
  by_cases h : other = coordinate
  · subst other
    simp [hammingSupport, flipToThird,
      Ne.symm (thirdQuestion_ne_right
        (center coordinate) (clause coordinate))]
  · simp [hammingSupport, flipToThird, h]

private theorem centerSupport_flipToThird
    (center clause : FourByThreeClause)
    (coordinate : FourByThreePlayer)
    (hcoordinate : coordinate ∈ hammingSupport center clause) :
    hammingSupport center (flipToThird center clause coordinate) =
      hammingSupport center clause := by
  ext other
  by_cases h : other = coordinate
  · subst other
    have hcenterClause : center coordinate ≠ clause coordinate := by
      simpa [hammingSupport] using hcoordinate
    simp [hammingSupport, flipToThird,
      Ne.symm (thirdQuestion_ne_left
        (center coordinate) (clause coordinate)),
      hcenterClause]
  · simp [hammingSupport, flipToThird, h]

private theorem flipToThird_in_layerTwoBallSlice
    (center clause : FourByThreeClause)
    (hclause : hammingDistance center clause = 2)
    (coordinate : FourByThreePlayer)
    (hcoordinate : coordinate ∈ hammingSupport center clause) :
    flipToThird center clause coordinate ∈
      layerTwoBallSlice center clause := by
  apply Finset.mem_inter.mpr
  constructor
  · simp only [radiusOneBall, closedHammingBall, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [← hammingSupport_card, hammingSupport_flipToThird]
    simp
  · simp only [hammingSphere, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hammingSupport_card,
      centerSupport_flipToThird center clause coordinate hcoordinate,
      hammingSupport_card]
    exact hclause

/--
The radius-one ball of a layer-two clause meets that layer in exactly three
points.
-/
theorem layerTwo_ball_slice_card_eq_three
    (center clause : FourByThreeClause)
    (hclause : hammingDistance center clause = 2) :
    (radiusOneBall clause ∩ hammingSphere center 2).card = 3 := by
  let clauseSupport := hammingSupport center clause
  let flips :=
    clauseSupport.image (flipToThird center clause)
  let witnesses := insert clause flips
  have hflipInjective :
      Function.Injective (flipToThird center clause) := by
    intro a b hab
    have hsupports :=
      congrArg (hammingSupport clause) hab
    rw [hammingSupport_flipToThird,
      hammingSupport_flipToThird] at hsupports
    exact Finset.singleton_inj.mp hsupports
  have hflipsCard : flips.card = 2 := by
    change
      (clauseSupport.image
        (flipToThird center clause)).card = 2
    rw [Finset.card_image_of_injective _ hflipInjective]
    simpa [clauseSupport] using hclause
  have hclauseNotFlips : clause ∉ flips := by
    change
      clause ∉ clauseSupport.image
        (flipToThird center clause)
    intro hclauseFlip
    obtain ⟨coordinate, _hcoordinate, heq⟩ :=
      Finset.mem_image.mp hclauseFlip
    have hsupports :=
      congrArg (hammingSupport clause) heq
    rw [hammingSupport_flipToThird] at hsupports
    simp [hammingSupport] at hsupports
  have hwitnessesCard : witnesses.card = 3 := by
    change (insert clause flips).card = 3
    rw [Finset.card_insert_of_notMem hclauseNotFlips,
      hflipsCard]
  have hwitnessesSubset :
      witnesses ⊆ layerTwoBallSlice center clause := by
    intro point hpoint
    rcases Finset.mem_insert.mp hpoint with rfl | hpoint
    · apply Finset.mem_inter.mpr
      constructor
      · simp [radiusOneBall, closedHammingBall]
      · simpa [hammingSphere] using hclause
    · obtain ⟨coordinate, hcoordinate, rfl⟩ :=
        Finset.mem_image.mp hpoint
      exact flipToThird_in_layerTwoBallSlice
        center clause hclause coordinate hcoordinate
  apply Nat.le_antisymm
  · exact layerTwo_ball_slice_card_le_three center clause hclause
  · change 3 ≤ (layerTwoBallSlice center clause).card
    rw [← hwitnessesCard]
    exact Finset.card_le_card hwitnessesSubset

/-- Hamming distance on four-by-three clauses satisfies the triangle inequality. -/
theorem hammingDistance_triangle
    (x y z : FourByThreeClause) :
    hammingDistance x z ≤
      hammingDistance x y + hammingDistance y z := by
  have hsubset :
      hammingSupport x z ⊆
        hammingSupport x y ∪ hammingSupport y z := by
    intro coordinate hcoordinate
    have hxz : x coordinate ≠ z coordinate := by
      simpa [hammingSupport] using hcoordinate
    by_contra hnot
    simp only [Finset.mem_union, not_or] at hnot
    have hxy : x coordinate = y coordinate := by
      simpa [hammingSupport] using hnot.1
    have hyz : y coordinate = z coordinate := by
      simpa [hammingSupport] using hnot.2
    exact hxz (hxy.trans hyz)
  calc
    hammingDistance x z = (hammingSupport x z).card := rfl
    _ ≤ (hammingSupport x y ∪ hammingSupport y z).card :=
      Finset.card_le_card hsubset
    _ ≤
        (hammingSupport x y).card +
          (hammingSupport y z).card :=
      Finset.card_union_le _ _
    _ =
        hammingDistance x y + hammingDistance y z := rfl

/--
Four layer-two clauses cover at most twelve points of the layer-two sphere.

The statement is stronger than the labeled-four-cycle application: disjointness
of the four ball slices is not needed for this upper bound.
-/
theorem four_layerTwo_balls_cover_at_most_twelve
    (center : FourByThreeClause) (clauses : Finset FourByThreeClause)
    (hcard : clauses.card = 4)
    (hlayer :
      ∀ clause ∈ clauses, hammingDistance center clause = 2) :
    (clauses.biUnion fun clause =>
      radiusOneBall clause ∩ hammingSphere center 2).card ≤ 12 := by
  have hcover :=
    Finset.card_biUnion_le_card_mul clauses
      (fun clause => radiusOneBall clause ∩ hammingSphere center 2) 3
      (fun clause hclause =>
        layerTwo_ball_slice_card_le_three center clause
          (hlayer clause hclause))
  rw [hcard] at hcover
  exact hcover

/--
Four pairwise distance-three layer-two clauses cover exactly twelve distinct
layer-two points.  A labeled four-cycle has precisely this separation
property, so this is the reusable Hamming-geometric core of that argument.
-/
theorem four_separated_layerTwo_balls_cover_exactly_twelve
    (center : FourByThreeClause) (clauses : Finset FourByThreeClause)
    (hcard : clauses.card = 4)
    (hlayer :
      ∀ clause ∈ clauses, hammingDistance center clause = 2)
    (hseparated :
      ∀ ⦃x⦄, x ∈ clauses → ∀ ⦃y⦄, y ∈ clauses → x ≠ y →
        3 ≤ hammingDistance x y) :
    (clauses.biUnion fun clause =>
      radiusOneBall clause ∩ hammingSphere center 2).card = 12 := by
  have hpairwise :
      (clauses : Set FourByThreeClause).PairwiseDisjoint
        (fun clause =>
          radiusOneBall clause ∩ hammingSphere center 2) := by
    intro x hx y hy hxy
    have hinterCard :
        (radiusOneBall x ∩ radiusOneBall y).card = 0 :=
      radiusOneBall_inter_card_of_three_le x y
        (hseparated hx hy hxy)
    have hballs :
        Disjoint (radiusOneBall x) (radiusOneBall y) := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact Finset.card_eq_zero.mp hinterCard
    exact hballs.mono (Finset.inter_subset_left)
      (Finset.inter_subset_left)
  rw [Finset.card_biUnion hpairwise]
  calc
    (∑ clause ∈ clauses,
        (radiusOneBall clause ∩ hammingSphere center 2).card) =
        ∑ _clause ∈ clauses, 3 := by
      apply Finset.sum_congr rfl
      intro clause hclause
      exact layerTwo_ball_slice_card_eq_three
        center clause (hlayer clause hclause)
    _ = 12 := by simp [hcard]

/--
If every support clause lies either in a specified four-element layer-two
family or in layer four about a center, then the support has at least thirteen
safe centers.

In the nine-clause application the remaining five clauses are in layer four.
The proof only needs that such clauses cover no layer-two points: the four
layer-two balls cover at most twelve of the 24 layer-two points, and the
original center supplies one more safe point.
-/
theorem four_layerTwo_five_layerFour_safeCenters_card_ge_thirteen
    (center : FourByThreeClause)
    (support layerTwoClauses : Finset FourByThreeClause)
    (hlayerTwoCard : layerTwoClauses.card = 4)
    (hlayerTwo :
      ∀ clause ∈ layerTwoClauses,
        hammingDistance center clause = 2)
    (hsupportLayers :
      ∀ clause ∈ support,
        clause ∈ layerTwoClauses ∨
          hammingDistance center clause = 4) :
    13 ≤ (safeCenters support).card := by
  let layerTwoSphere := hammingSphere center 2
  let safeLayerTwo := layerTwoSphere ∩ safeCenters support
  let unsafeLayerTwo := layerTwoSphere \ safeCenters support
  let coveredByLayerTwo :=
    layerTwoClauses.biUnion fun clause =>
      radiusOneBall clause ∩ layerTwoSphere
  have hcoveredCard : coveredByLayerTwo.card ≤ 12 := by
    simpa [coveredByLayerTwo, layerTwoSphere] using
      four_layerTwo_balls_cover_at_most_twelve
        center layerTwoClauses hlayerTwoCard hlayerTwo
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
    have hclauseLayerTwo : clause ∈ layerTwoClauses := by
      by_contra hnotLayerTwo
      have hfour : hammingDistance center clause = 4 := by
        rcases hsupportLayers clause hclauseSupport with hin | hfour
        · exact False.elim (hnotLayerTwo hin)
        · exact hfour
      have htriangle :=
        hammingDistance_triangle center point clause
      omega
    apply Finset.mem_biUnion.mpr
    refine ⟨clause, hclauseLayerTwo, ?_⟩
    apply Finset.mem_inter.mpr
    constructor
    · simp only [radiusOneBall, closedHammingBall, Finset.mem_filter,
        Finset.mem_univ, true_and]
      rw [hammingDistance_comm]
      exact hclauseNear'
    · exact hpointSphere
  have hunsafeCard : unsafeLayerTwo.card ≤ 12 :=
    (Finset.card_le_card hunsafeSubset).trans hcoveredCard
  have hsphereCard : layerTwoSphere.card = 24 := by
    simp [layerTwoSphere]
  have hsafeLayerCard : 12 ≤ safeLayerTwo.card := by
    have hpartitionCard :=
      Finset.card_sdiff_add_card_inter
        layerTwoSphere (safeCenters support)
    change unsafeLayerTwo.card + safeLayerTwo.card =
      layerTwoSphere.card at hpartitionCard
    omega
  have hcenterSafe : center ∈ safeCenters support := by
    simp only [safeCenters, Finset.mem_filter, Finset.mem_univ, true_and]
    intro clause hclause
    rcases hsupportLayers clause hclause with hclauseLayerTwo | hclauseLayerFour
    · rw [hlayerTwo clause hclauseLayerTwo]
    · rw [hclauseLayerFour]
      omega
  have hcenterNotLayerTwo : center ∉ safeLayerTwo := by
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
      (insert center safeLayerTwo).card = safeLayerTwo.card + 1 := by
    rw [Finset.card_insert_of_notMem hcenterNotLayerTwo]
  have hcard :=
    Finset.card_le_card hinsertSubset
  omega

/-- The number of support balls covering a point. -/
def coverageMultiplicity
    (support : Finset FourByThreeClause)
    (point : FourByThreeClause) : Nat :=
  (support.filter fun clause => hammingDistance point clause ≤ 1).card

private theorem coverageMultiplicity_pos_iff_not_safe
    (support : Finset FourByThreeClause)
    (point : FourByThreeClause) :
    0 < coverageMultiplicity support point ↔
      point ∉ safeCenters support := by
  constructor
  · intro hpositive hsafe
    have hnonempty :
        (support.filter fun clause =>
          hammingDistance point clause ≤ 1).Nonempty :=
      Finset.card_pos.mp (by
        simpa [coverageMultiplicity] using hpositive)
    obtain ⟨clause, hclause⟩ := hnonempty
    have hclauseData := Finset.mem_filter.mp hclause
    have hclauseSupport : clause ∈ support := hclauseData.1
    have hnear' : hammingDistance point clause ≤ 1 :=
      hclauseData.2
    have hfar :
        2 ≤ hammingDistance point clause :=
      (Finset.mem_filter.mp hsafe).2 clause hclauseSupport
    omega
  · intro hnotSafe
    have hnotAll :
        ¬ ∀ clause ∈ support,
            2 ≤ hammingDistance point clause := by
      simpa [safeCenters] using hnotSafe
    push Not at hnotAll
    obtain ⟨clause, hclauseSupport, hnear⟩ := hnotAll
    rw [coverageMultiplicity]
    apply Finset.card_pos.mpr
    exact ⟨clause, Finset.mem_filter.mpr ⟨hclauseSupport, by omega⟩⟩

private theorem total_coverageMultiplicity
    (support : Finset FourByThreeClause) :
    ∑ point : FourByThreeClause,
        coverageMultiplicity support point =
      9 * support.card := by
  let covers : FourByThreeClause → FourByThreeClause → Prop :=
    fun clause point => hammingDistance point clause ≤ 1
  have hdouble :=
    Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      covers
      (s := support)
      (t := (Finset.univ : Finset FourByThreeClause))
  have hdouble' :
      (∑ clause ∈ support,
          ((Finset.univ : Finset FourByThreeClause).filter
            fun point => covers clause point).card) =
        ∑ point : FourByThreeClause,
          coverageMultiplicity support point := by
    simpa [Finset.bipartiteAbove, Finset.bipartiteBelow,
      coverageMultiplicity, covers] using hdouble
  rw [← hdouble']
  calc
    (∑ clause ∈ support,
        ((Finset.univ : Finset FourByThreeClause).filter
          fun point => covers clause point).card) =
        ∑ _clause ∈ support, 9 := by
      apply Finset.sum_congr rfl
      intro clause _hclause
      have hball :
          (Finset.univ : Finset FourByThreeClause).filter
              (fun point => covers clause point) =
            radiusOneBall clause := by
        ext point
        simp [covers, radiusOneBall, closedHammingBall,
          hammingDistance_comm]
      rw [hball, radiusOneBall_card]
    _ = 9 * support.card := by
      simp [Nat.mul_comm]

/--
The global coverage-excess identity

`Σ_{r(y)>0} (r(y)-1) = 9|S| - 81 + |U|`

for radius-one balls in the 81-point four-by-three Hamming space.  Integers
are used so that the displayed subtraction has its ordinary algebraic
meaning even for very small supports.
-/
theorem coverageExcess_identity
    (support : Finset FourByThreeClause) :
    (∑ point ∈
        (Finset.univ.filter fun point : FourByThreeClause =>
          0 < coverageMultiplicity support point),
        ((coverageMultiplicity support point : ℤ) - 1)) =
      9 * (support.card : ℤ) - 81 +
        ((safeCenters support).card : ℤ) := by
  let covered :=
    Finset.univ.filter fun point : FourByThreeClause =>
      0 < coverageMultiplicity support point
  have hcovered :
      covered =
        (Finset.univ : Finset FourByThreeClause) \ safeCenters support := by
    ext point
    simp only [covered, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    rw [coverageMultiplicity_pos_iff_not_safe]
  have hcoveredCard :
      covered.card + (safeCenters support).card = 81 := by
    rw [hcovered]
    have hsubset :
        safeCenters support ⊆
          (Finset.univ : Finset FourByThreeClause) :=
      Finset.filter_subset _ _
    rw [Finset.card_sdiff_add_card_eq_card hsubset]
    exact fourByThreeClause_card
  have hsumCovered :
      (∑ point ∈ covered,
          coverageMultiplicity support point) =
        ∑ point : FourByThreeClause,
          coverageMultiplicity support point := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro point _hpoint hpointNotCovered
    have hnotPositive :
        ¬ 0 < coverageMultiplicity support point := by
      simpa [covered] using hpointNotCovered
    omega
  have hsumCoveredInt :
      (∑ point ∈ covered,
          (coverageMultiplicity support point : ℤ)) =
        9 * (support.card : ℤ) := by
    exact_mod_cast hsumCovered.trans (total_coverageMultiplicity support)
  have hcoveredCardInt :
      (covered.card : ℤ) + ((safeCenters support).card : ℤ) = 81 := by
    exact_mod_cast hcoveredCard
  change
    (∑ point ∈ covered,
        ((coverageMultiplicity support point : ℤ) - 1)) =
      9 * (support.card : ℤ) - 81 +
        ((safeCenters support).card : ℤ)
  rw [Finset.sum_sub_distrib, hsumCoveredInt]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  omega

/--
Excess on pairwise disjoint local neighborhoods is bounded by the global
excess on any covered ambient set containing them.

This finite-set lemma is the abstract bookkeeping step in the safe-hole
neighborhood argument; the application takes `multiplicity` to be
`coverageMultiplicity`.
-/
theorem pairwiseDisjoint_neighborhood_excess_le_global
    {Center Point : Type*}
    (centers : Finset Center) (covered : Finset Point)
    (neighborhood : Center → Finset Point)
    (multiplicity : Point → Nat)
    (hpairwise :
      (centers : Set Center).PairwiseDisjoint neighborhood)
    (hcontained :
      ∀ center ∈ centers, neighborhood center ⊆ covered)
    (hpositive :
      ∀ point ∈ covered, 1 ≤ multiplicity point) :
    (∑ center ∈ centers,
        ∑ point ∈ neighborhood center,
          ((multiplicity point : ℤ) - 1)) ≤
      ∑ point ∈ covered, ((multiplicity point : ℤ) - 1) := by
  classical
  let localUnion := centers.biUnion neighborhood
  have hunionSubset : localUnion ⊆ covered := by
    intro point hpoint
    obtain ⟨center, hcenter, hpointNeighborhood⟩ :=
      Finset.mem_biUnion.mp hpoint
    exact hcontained center hcenter hpointNeighborhood
  calc
    (∑ center ∈ centers,
        ∑ point ∈ neighborhood center,
          ((multiplicity point : ℤ) - 1)) =
        ∑ point ∈ localUnion,
          ((multiplicity point : ℤ) - 1) := by
      exact (Finset.sum_biUnion hpairwise).symm
    _ ≤
        ∑ point ∈ covered,
          ((multiplicity point : ℤ) - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hunionSubset
      intro point hpointCovered _hpointNotLocal
      have hpointPositive := hpositive point hpointCovered
      omega

end

end XORGame
end QIT

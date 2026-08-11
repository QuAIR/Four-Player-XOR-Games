/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Circuit
public import XORGameFormalization.Hamming
public import Mathlib.Data.Fintype.EquivFin

/-!
# Nine radius-one Hamming balls force incidence independence

Nine distinct radius-one balls in the 81-word space `(Fin 4 → Fin 3)` have
total size 81.  If they cover the space, the ball-to-point projection is a
bijection, so the centers have pairwise Hamming distance at least three.
Every projection to two player coordinates is then a bijection with
`Fin 3 × Fin 3`.

The final independence proof is structural.  Pairwise uniformity implies
that every center agrees with every other center in exactly one coordinate.
Consequently, for each center `e`,

`∑ a, incidenceColumn (a, query e a) - 1 = 3 * delta_e`.

Thus the incidence columns span all functions on the nine centers, and the
incidence rows are linearly independent.  No circuit-support enumeration is
used.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- The radius-one balls centered at `query e` cover the full clause space. -/
def RadiusOneBallsCover {E : Type uE}
    (query : E → FourByThreeClause) : Prop :=
  ∀ point : FourByThreeClause,
    ∃ e : E, point ∈ radiusOneBall (query e)

/-- A center together with a point in its radius-one Hamming ball. -/
abbrev RadiusOneBallPoint {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :=
  Σ e : E, ↥(radiusOneBall (query e))

/-- Forget the center of a point marked by a radius-one ball. -/
def radiusOneBallPointProjection {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :
    RadiusOneBallPoint query → FourByThreeClause :=
  fun markedPoint => markedPoint.2.1

/--
For nine centers, coverage makes the marked-ball-point projection injective:
both its domain and codomain have cardinality 81.
-/
theorem radiusOneBallPointProjection_injective_of_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query) :
    Function.Injective (radiusOneBallPointProjection query) := by
  classical
  have hsurjective :
      Function.Surjective (radiusOneBallPointProjection query) := by
    intro point
    obtain ⟨e, he⟩ := hcover point
    exact ⟨⟨e, ⟨point, he⟩⟩, rfl⟩
  have hdomain :
      Fintype.card (RadiusOneBallPoint query) = 81 := by
    rw [Fintype.card_sigma]
    simp [hcard]
  exact
    ((Fintype.bijective_iff_surjective_and_card
      (radiusOneBallPointProjection query)).2
      ⟨hsurjective, by simp [hdomain]⟩).1

/-- Distinct balls in a nine-ball cover are pairwise disjoint. -/
theorem radiusOneBalls_pairwise_disjoint_of_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query) :
    ∀ ⦃e f : E⦄, e ≠ f →
      Disjoint (radiusOneBall (query e)) (radiusOneBall (query f)) := by
  classical
  have hinjective :=
    radiusOneBallPointProjection_injective_of_cover query hcard hcover
  intro e f hef
  rw [Finset.disjoint_left]
  intro point he hf
  apply hef
  have hmarked :
      (⟨e, ⟨point, he⟩⟩ : RadiusOneBallPoint query) =
        ⟨f, ⟨point, hf⟩⟩ := by
    apply hinjective
    rfl
  exact congrArg Sigma.fst hmarked

/--
Distinct centers in a nine-ball cover have Hamming distance at least three.
-/
theorem hammingDistance_three_le_of_nine_ball_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query)
    {e f : E} (hef : e ≠ f) :
    3 ≤ hammingDistance (query e) (query f) := by
  classical
  have hdisjoint :=
    radiusOneBalls_pairwise_disjoint_of_cover query hcard hcover hef
  have hinter :
      radiusOneBall (query e) ∩ radiusOneBall (query f) = ∅ :=
    Finset.disjoint_iff_inter_eq_empty.mp hdisjoint
  have hzero :
      (radiusOneBall (query e) ∩ radiusOneBall (query f)).card = 0 := by
    rw [hinter]
    simp
  by_contra hthree
  have hle : hammingDistance (query e) (query f) ≤ 2 := by omega
  generalize hdistance :
      hammingDistance (query e) (query f) = distance at hle hzero
  interval_cases distance <;>
    simp [radiusOneBall_inter_card, hdistance] at hzero

/-- Projection of a clause support onto two chosen player coordinates. -/
def pairProjection {E : Type uE}
    (query : E → FourByThreeClause) (a b : Fin 4) :
    E → Fin 3 × Fin 3 :=
  fun e => (query e a, query e b)

private theorem hammingDistance_le_two_of_pairProjection_eq
    {x y : FourByThreeClause} {a b : Fin 4} (hab : a ≠ b)
    (hprojection : (x a, x b) = (y a, y b)) :
    hammingDistance x y ≤ 2 := by
  classical
  have ha : x a = y a := congrArg Prod.fst hprojection
  have hb : x b = y b := congrArg Prod.snd hprojection
  have hsubset :
      (Finset.univ.filter fun coordinate : Fin 4 =>
        x coordinate ≠ y coordinate) ⊆
        (Finset.univ.erase a).erase b := by
    intro coordinate hcoordinate
    have hdiff := (Finset.mem_filter.mp hcoordinate).2
    have hneA : coordinate ≠ a := by
      intro h
      subst coordinate
      exact hdiff ha
    have hneB : coordinate ≠ b := by
      intro h
      subst coordinate
      exact hdiff hb
    exact Finset.mem_erase.mpr
      ⟨hneB, Finset.mem_erase.mpr ⟨hneA, Finset.mem_univ _⟩⟩
  unfold hammingDistance
  calc
    (Finset.univ.filter fun coordinate : Fin 4 =>
      x coordinate ≠ y coordinate).card ≤
        ((Finset.univ : Finset (Fin 4)).erase a |>.erase b).card :=
      Finset.card_le_card hsubset
    _ = 2 := by
      have hbmem :
          b ∈ (Finset.univ : Finset (Fin 4)).erase a :=
        Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
      rw [Finset.card_erase_of_mem hbmem,
        Finset.card_erase_of_mem (Finset.mem_univ a)]
      simp

/--
Every two-coordinate projection of the centers in a nine-ball cover is a
bijection with the nine ordered ternary pairs.
-/
theorem pairProjection_bijective_of_nine_ball_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query)
    {a b : Fin 4} (hab : a ≠ b) :
    Function.Bijective (pairProjection query a b) := by
  apply (Fintype.bijective_iff_injective_and_card
    (pairProjection query a b)).2
  constructor
  · intro e f hprojection
    by_contra hef
    have hthree :=
      hammingDistance_three_le_of_nine_ball_cover
        query hcard hcover hef
    have htwo :=
      hammingDistance_le_two_of_pairProjection_eq hab hprojection
    omega
  · simp [hcard]

/-- A canonical player coordinate different from the supplied coordinate. -/
private def otherCoordinate : Fin 4 → Fin 4
  | 0 => 1
  | _ => 0

private theorem otherCoordinate_ne (a : Fin 4) :
    otherCoordinate a ≠ a := by
  fin_cases a <;> simp [otherCoordinate, Fin.ext_iff]

/--
Every question occurs at exactly three centers on each player coordinate of
a nine-ball cover.
-/
theorem questionFiber_card_three_of_nine_ball_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query)
    (a : Fin 4) (question : Fin 3) :
    (Finset.univ.filter fun e : E =>
      query e a = question).card = 3 := by
  classical
  let projectionEquiv : E ≃ Fin 3 × Fin 3 :=
    Equiv.ofBijective
      (pairProjection query a (otherCoordinate a))
      (pairProjection_bijective_of_nine_ball_cover
        query hcard hcover (otherCoordinate_ne a).symm)
  rw [Finset.card_filter]
  have hsum :=
    Fintype.sum_equiv projectionEquiv
      (fun e : E => if query e a = question then 1 else 0)
      (fun pair : Fin 3 × Fin 3 =>
        if pair.1 = question then 1 else 0)
      (fun e => by simp [projectionEquiv, pairProjection])
  rw [hsum]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ]
  fin_cases question <;>
    norm_num [Fin.ext_iff]

/-- The number of player coordinates on which two clauses agree. -/
def agreementCount (x y : FourByThreeClause) : Nat :=
  (Finset.univ.filter fun coordinate : Fin 4 =>
    x coordinate = y coordinate).card

/-- Agreement and Hamming-disagreement counts partition the four coordinates. -/
theorem agreementCount_add_hammingDistance
    (x y : FourByThreeClause) :
    agreementCount x y + hammingDistance x y = 4 := by
  simpa [agreementCount, hammingDistance] using
    (Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin 4)))
      (fun coordinate => x coordinate = y coordinate))

@[simp]
theorem agreementCount_self (x : FourByThreeClause) :
    agreementCount x x = 4 := by
  simp [agreementCount]

/--
The total number of coordinate agreements with one fixed center is twelve:
each of four question fibers has size three.
-/
theorem sum_agreementCount_eq_twelve_of_nine_ball_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query)
    (e : E) :
    ∑ f : E, agreementCount (query f) (query e) = 12 := by
  classical
  simp_rw [agreementCount, Finset.card_filter]
  rw [Finset.sum_comm]
  simp_rw [← Finset.card_filter]
  simp [questionFiber_card_three_of_nine_ball_cover
    query hcard hcover]

private theorem eq_one_of_sum_eq_card_of_le_one
    {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → Nat)
    (hsum : ∑ x ∈ s, f x = s.card)
    (hle : ∀ x ∈ s, f x ≤ 1) :
    ∀ x ∈ s, f x = 1 := by
  intro x hx
  have hbound :
      ∑ y ∈ s.erase x, f y ≤ (s.erase x).card := by
    calc
      ∑ y ∈ s.erase x, f y ≤ ∑ _y ∈ s.erase x, 1 :=
        Finset.sum_le_sum fun y hy => hle y (Finset.mem_of_mem_erase hy)
      _ = (s.erase x).card := by simp
  have hdecomp :
      (∑ y ∈ s.erase x, f y) + f x = s.card := by
    rw [Finset.sum_erase_add s f hx, hsum]
  have hcardErase : (s.erase x).card + 1 = s.card := by
    rw [Finset.card_erase_of_mem hx]
    have hcardPos : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega
  have hxle := hle x hx
  omega

/--
Any two distinct centers in a nine-ball cover agree in exactly one player
coordinate (and hence have Hamming distance exactly three).
-/
theorem agreementCount_eq_one_of_nine_ball_cover
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query)
    {e f : E} (hef : e ≠ f) :
    agreementCount (query f) (query e) = 1 := by
  classical
  let others : Finset E := Finset.univ.erase e
  have htotal :=
    sum_agreementCount_eq_twelve_of_nine_ball_cover
      query hcard hcover e
  have hsumOthers :
      ∑ g ∈ others, agreementCount (query g) (query e) = 8 := by
    have hsplit :=
      Finset.sum_erase_add
        Finset.univ
        (fun g : E => agreementCount (query g) (query e))
        (Finset.mem_univ e)
    simp only [others] at hsplit ⊢
    rw [htotal, agreementCount_self] at hsplit
    omega
  have hcardOthers : others.card = 8 := by
    simp [others, hcard]
  have hle :
      ∀ g ∈ others, agreementCount (query g) (query e) ≤ 1 := by
    intro g hg
    have hge : g ≠ e := (Finset.mem_erase.mp hg).1
    have hdistance :=
      hammingDistance_three_le_of_nine_ball_cover
        query hcard hcover hge
    have hpartition :=
      agreementCount_add_hammingDistance (query g) (query e)
    omega
  have hone :=
    eq_one_of_sum_eq_card_of_le_one others
      (fun g => agreementCount (query g) (query e))
      (by simpa [hcardOthers] using hsumOthers) hle
  exact hone f (Finset.mem_erase.mpr ⟨hef.symm, Finset.mem_univ f⟩)

/--
The sum of the four incidence columns selected by a center counts coordinate
agreements with that center.
-/
theorem sum_selected_incidence_eq_agreementCount
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (e f : E) :
    ∑ a : Fin 4,
      rationalIncidence query f (a, query e a) =
        (agreementCount (query f) (query e) : ℚ) := by
  rw [agreementCount, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : query f a = query e a <;>
    simp [rationalIncidence, incidence, h]

/--
Nine distinct radius-one balls covering the full ternary clause space force
the rational incidence rows to be linearly independent.
-/
theorem nineBallCover_rationalIncidence_linearIndependent
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hcover : RadiusOneBallsCover query) :
    LinearIndependent ℚ (rationalIncidence query).row := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro coefficient hrelation e
  have hcolumn :
      ∀ a : Fin 4, ∀ question : Fin 3,
        ∑ f : E,
          coefficient f *
            rationalIncidence query f (a, question) = 0 := by
    intro a question
    have hcoordinate := congrFun hrelation (a, question)
    simpa [Matrix.row, smul_eq_mul] using hcoordinate
  have htotal : ∑ f : E, coefficient f = 0 := by
    calc
      ∑ f : E, coefficient f =
          ∑ f : E,
            coefficient f *
              (∑ question : Fin 3,
                rationalIncidence query f (0, question)) := by
        apply Finset.sum_congr rfl
        intro f _
        rw [rationalIncidence_hasFourByThreeIncidenceSums query f 0]
        simp
      _ = ∑ f : E, ∑ question : Fin 3,
            coefficient f *
              rationalIncidence query f (0, question) := by
        simp_rw [Finset.mul_sum]
      _ = ∑ question : Fin 3, ∑ f : E,
            coefficient f *
              rationalIncidence query f (0, question) := by
        rw [Finset.sum_comm]
      _ = 0 := by simp [hcolumn]
  have hscore :
      ∀ f : E,
        (∑ a : Fin 4,
          rationalIncidence query f (a, query e a)) - 1 =
            if f = e then 3 else 0 := by
    intro f
    rw [sum_selected_incidence_eq_agreementCount]
    by_cases hfe : f = e
    · subst f
      norm_num
    · rw [agreementCount_eq_one_of_nine_ball_cover
        query hcard hcover (e := e) (f := f) (Ne.symm hfe)]
      simp [hfe]
  have hscoreSum :
      ∑ f : E,
        coefficient f *
          ((∑ a : Fin 4,
            rationalIncidence query f (a, query e a)) - 1) = 0 := by
    simp_rw [mul_sub, mul_one, Finset.mul_sum]
    rw [Finset.sum_sub_distrib, Finset.sum_comm]
    simp [hcolumn, htotal]
  simp_rw [hscore] at hscoreSum
  simp at hscoreSum
  linarith

/--
Every nine-clause full rational circuit has a safe center: a ternary
four-player clause at Hamming distance at least two from every support
clause.
-/
theorem nineClause_fullCircuit_has_safeCenter
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 9)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    ∃ center : FourByThreeClause,
      ∀ e : E, 2 ≤ hammingDistance center (query e) := by
  classical
  by_contra hsafe
  push Not at hsafe
  have hcover : RadiusOneBallsCover query := by
    intro center
    obtain ⟨e, he⟩ := hsafe center
    refine ⟨e, ?_⟩
    simp only [radiusOneBall, closedHammingBall, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rw [hammingDistance_comm]
    omega
  exact hCircuit.1
    (nineBallCover_rationalIncidence_linearIndependent
      query hcard hcover)

end

end XORGame
end QIT

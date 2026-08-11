/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.CircuitGeneration
public import XORGameFormalization.RankBoundary
import Mathlib.RingTheory.Localization.Module

/-!
# Primitive integer circuits as full rational support circuits

This module bridges the integral circuit-generation API to the rational rank
and page-profile API.  A support-minimal integer incidence relation remains
minimal after passage to `ℚ`: Mathlib's fraction-ring linear-independence
theorem performs the required clearing of denominators.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- A primitive circuit has a nonempty coefficient support. -/
theorem primitiveKernelCircuit_integerSupport_nonempty
    {E : Type uE} {C : Type*} [Fintype E]
    (φ : (E → ℤ) →+ (C → ℤ)) (c : E → ℤ)
    (hc : IsPrimitiveKernelCircuit φ c) :
    (integerSupport c).Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hempty
  exact hc.1.2.1
    ((integerSupport_eq_empty_iff c).mp hempty)

/-- Every coefficient on the restricted integer support is nonzero. -/
theorem integerSupport_coefficient_ne_zero
    {E : Type uE} [Fintype E]
    (c : E → ℤ) (clause : ↥(integerSupport c)) :
    c clause.1 ≠ 0 :=
  mem_integerSupport.mp clause.2

/-- Restrict a clause map to the nonzero coordinates of an integer vector. -/
def restrictQueryToIntegerSupport
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ) :
    ↥(integerSupport c) → FourByThreeClause :=
  fun clause => query clause.1

/-- Restriction to a coefficient support preserves distinct clauses. -/
theorem restrictQueryToIntegerSupport_injective
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hquery : Function.Injective query) :
    Function.Injective (restrictQueryToIntegerSupport query c) := by
  intro left right heq
  apply Subtype.ext
  exact hquery heq

/-- An integer relation remains a relation after deleting its zero coordinates. -/
theorem integerRelation_restrictQueryToIntegerSupport
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc : IsIntegerRelation query c) :
    IsIntegerRelation
      (restrictQueryToIntegerSupport query c)
      (fun clause : ↥(integerSupport c) => c clause.1) := by
  classical
  intro pq
  change
    (∑ clause : ↥(integerSupport c),
      incidence query clause.1 pq * c clause.1) = 0
  calc
    (∑ clause : ↥(integerSupport c),
        incidence query clause.1 pq * c clause.1) =
        ∑ clause ∈ integerSupport c,
          incidence query clause pq * c clause := by
      rw [Finset.sum_subtype
        (s := integerSupport c)
        (h := fun _ => Iff.rfl)
        (f := fun clause =>
          incidence query clause pq * c clause)]
    _ = ∑ clause : E,
          incidence query clause pq * c clause := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro clause _hclauseUniv hclauseSupport
      have hzero : c clause = 0 := by
        simpa [mem_integerSupport] using hclauseSupport
      simp [hzero]
    _ = 0 := hc pq

/-- Every primitive incidence circuit is, in particular, an integer relation. -/
theorem primitiveKernelCircuit_isIntegerRelation
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c) :
    IsIntegerRelation query c :=
  (isIntegerRelation_iff_mem_incidenceRelationHom_ker
    query c).mpr hc.1.1

/-- The nonzero restriction of a primitive circuit remains an integer relation. -/
theorem primitiveKernelCircuit_restricted_isIntegerRelation
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c) :
    IsIntegerRelation
      (restrictQueryToIntegerSupport query c)
      (fun clause : ↥(integerSupport c) => c clause.1) :=
  integerRelation_restrictQueryToIntegerSupport
    query c (primitiveKernelCircuit_isIntegerRelation query c hc)

/-- Extend integer coefficients on `integerSupport c` by zero. -/
def extendIntegerSupportCoefficients
    {E : Type uE} [Fintype E]
    (c : E → ℤ) (coefficient : ↥(integerSupport c) → ℤ) :
    E → ℤ := by
  classical
  exact fun e =>
    if he : e ∈ integerSupport c then coefficient ⟨e, he⟩ else 0

@[simp]
theorem extendIntegerSupportCoefficients_apply
    {E : Type uE} [Fintype E]
    (c : E → ℤ) (coefficient : ↥(integerSupport c) → ℤ)
    (e : ↥(integerSupport c)) :
    extendIntegerSupportCoefficients c coefficient e.1 = coefficient e := by
  simp [extendIntegerSupportCoefficients]

theorem integerSupport_extendIntegerSupportCoefficients_subset
    {E : Type uE} [Fintype E]
    (c : E → ℤ) (coefficient : ↥(integerSupport c) → ℤ) :
    integerSupport (extendIntegerSupportCoefficients c coefficient) ⊆
      integerSupport c := by
  intro e he
  by_contra hec
  have hezero :
      extendIntegerSupportCoefficients c coefficient e = 0 := by
    simp [extendIntegerSupportCoefficients, hec]
  exact (mem_integerSupport.mp he) hezero

private theorem sum_restrictedRows_eq_cast_incidenceRelation
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (coefficient : ↥(integerSupport c) → ℤ) :
    (∑ clause : ↥(integerSupport c),
        coefficient clause •
          (rationalIncidence
            (restrictQueryToIntegerSupport query c)).row clause) =
      fun pq =>
        (incidenceRelationHom query
          (extendIntegerSupportCoefficients c coefficient) pq : ℚ) := by
  classical
  funext pq
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [incidenceRelationHom_apply, Int.cast_sum]
  have hrestrict :
      (∑ e : E,
          ((incidence query e pq *
            extendIntegerSupportCoefficients c coefficient e : ℤ) : ℚ)) =
        ∑ e ∈ integerSupport c,
          ((incidence query e pq *
            extendIntegerSupportCoefficients c coefficient e : ℤ) : ℚ) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _heUniv heSupport
    simp [extendIntegerSupportCoefficients, heSupport]
  rw [hrestrict]
  rw [Finset.sum_subtype
    (s := integerSupport c)
    (h := fun e => Iff.rfl)
    (f := fun e =>
      ((incidence query e pq *
        extendIntegerSupportCoefficients c coefficient e : ℤ) : ℚ))]
  apply Finset.sum_congr rfl
  intro clause _hclause
  simp [rationalIncidence, restrictQueryToIntegerSupport,
    extendIntegerSupportCoefficients, incidence]

private theorem restrictedRows_integerLinearIndependent_away
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (removed : ↥(integerSupport c)) :
    LinearIndependent ℤ
      (fun clause : {clause : ↥(integerSupport c) // clause ≠ removed} =>
        (rationalIncidence
          (restrictQueryToIntegerSupport query c)).row clause.1) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro coefficient hsum clause
  let supportCoefficient : ↥(integerSupport c) → ℤ :=
    fun i => if hi : i ≠ removed then coefficient ⟨i, hi⟩ else 0
  let extended : E → ℤ :=
    extendIntegerSupportCoefficients c supportCoefficient
  have hsumSupport :
      (∑ i : ↥(integerSupport c),
          supportCoefficient i •
            (rationalIncidence
              (restrictQueryToIntegerSupport query c)).row i) = 0 := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun i : ↥(integerSupport c) =>
        supportCoefficient i •
          (rationalIncidence
            (restrictQueryToIntegerSupport query c)).row i)
      removed]
    have hremoved : supportCoefficient removed = 0 := by
      simp [supportCoefficient]
    rw [hremoved, zero_smul, zero_add]
    calc
      (∑ i : {i : ↥(integerSupport c) // i ≠ removed},
          supportCoefficient i.1 •
            (rationalIncidence
              (restrictQueryToIntegerSupport query c)).row i.1) =
          ∑ i,
            coefficient i •
              (rationalIncidence
                (restrictQueryToIntegerSupport query c)).row i.1 := by
        apply Finset.sum_congr rfl
        intro i _hi
        simp [supportCoefficient, i.2]
      _ = 0 := hsum
  have hextendedKernel :
      incidenceRelationHom query extended = 0 := by
    funext pq
    have hcast :
        (incidenceRelationHom query extended pq : ℚ) = 0 := by
      have hrelation :=
        congrFun
          (sum_restrictedRows_eq_cast_incidenceRelation
            query c supportCoefficient) pq
      rw [hsumSupport] at hrelation
      simpa [extended] using hrelation.symm
    exact_mod_cast hcast
  have hextendedSupport :
      integerSupport extended ⊆ integerSupport c := by
    exact integerSupport_extendIntegerSupportCoefficients_subset
      c supportCoefficient
  have hextendedZero : extended = 0 := by
    by_contra hextended
    have hfullSupport :
        integerSupport c ⊆ integerSupport extended :=
      hc.1.2.2 extended hextendedKernel hextended hextendedSupport
    have hremovedExtended :
        extended removed.1 = 0 := by
      simp [extended, supportCoefficient]
    have hremovedMem :
        removed.1 ∈ integerSupport extended :=
      hfullSupport removed.2
    exact (mem_integerSupport.mp hremovedMem) hremovedExtended
  have hcoefficientExtended :
      extended clause.1.1 = coefficient clause := by
    simp [extended, supportCoefficient, clause.2]
  rw [← hcoefficientExtended, hextendedZero]
  rfl

/--
Restricting a primitive integer incidence circuit to its nonzero coordinates
gives a full rational circuit.
-/
theorem primitiveKernelCircuit_restricted_isFullRationalCircuit
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c) :
    IsFullRationalCircuit
      (rationalIncidence
        (restrictQueryToIntegerSupport query c)) := by
  classical
  have hcNonzero : c ≠ 0 := hc.1.2.1
  obtain ⟨e, he⟩ : ∃ e : E, c e ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hcNonzero
    funext e
    exact hall e
  let witness : ↥(integerSupport c) :=
    ⟨e, mem_integerSupport.mpr he⟩
  constructor
  · apply Fintype.not_linearIndependent_iff.mpr
    refine ⟨
      (fun clause : ↥(integerSupport c) => (c clause.1 : ℚ)),
      ?_, witness, ?_⟩
    · have hrelation :=
        sum_restrictedRows_eq_cast_incidenceRelation
          query c (fun clause => c clause.1)
      have hextension :
          extendIntegerSupportCoefficients c
              (fun clause : ↥(integerSupport c) => c clause.1) =
            c := by
        funext clause
        by_cases hclause : clause ∈ integerSupport c
        · simp [extendIntegerSupportCoefficients, hclause]
        · have hzero : c clause = 0 := by
            simpa [mem_integerSupport] using hclause
          simp [extendIntegerSupportCoefficients, hclause, hzero]
      rw [hextension, hc.1.1] at hrelation
      have hIntegerSum :
          (∑ clause : ↥(integerSupport c),
              c clause.1 •
                (rationalIncidence
                  (restrictQueryToIntegerSupport query c)).row clause) = 0 := by
        simpa using hrelation
      simpa [Int.cast_smul_eq_zsmul] using hIntegerSum
    · change (c e : ℚ) ≠ 0
      exact_mod_cast he
  · intro removed
    have hInteger :=
      restrictedRows_integerLinearIndependent_away
        query c hc removed
    exact
      (LinearIndependent.iff_fractionRing ℤ ℚ).mp hInteger

/-- Every primitive integer four-by-three incidence circuit has support at most ten. -/
theorem primitiveIncidenceCircuit_support_card_le_ten
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c) :
    (integerSupport c).card ≤ 10 := by
  letI : Nonempty ↥(integerSupport c) := by
    obtain ⟨e, he⟩ : ∃ e : E, c e ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hc.1.2.1 (funext hall)
    exact ⟨⟨e, mem_integerSupport.mpr he⟩⟩
  have hbound :=
    fourByThree_queryCircuit_card_le_ten
      (restrictQueryToIntegerSupport query c)
      (primitiveKernelCircuit_restricted_isFullRationalCircuit
        query c hc)
  rw [Fintype.card_coe] at hbound
  exact hbound

/-- A ten-clause primitive integer incidence circuit uses all questions on every page. -/
theorem tenClause_primitiveIncidenceCircuit_uses_all_questions
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (hcard : (integerSupport c).card = 10) :
    ∀ player : Fin 4,
      usedQuestionsCard
        (restrictQueryToIntegerSupport query c) player = 3 := by
  letI : Nonempty ↥(integerSupport c) := by
    have : 0 < (integerSupport c).card := by omega
    exact Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp this)
  apply tenClause_fullCircuit_uses_all_questions
    (restrictQueryToIntegerSupport query c)
  · rw [Fintype.card_coe]
    exact hcard
  · exact primitiveKernelCircuit_restricted_isFullRationalCircuit
      query c hc

/-- Every page of a nine-clause primitive integer circuit uses at least two questions. -/
theorem nineClause_primitiveIncidenceCircuit_uses_at_least_two_questions
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (hcard : (integerSupport c).card = 9) :
    ∀ player : Fin 4,
      2 ≤ usedQuestionsCard
        (restrictQueryToIntegerSupport query c) player := by
  letI : Nonempty ↥(integerSupport c) := by
    have : 0 < (integerSupport c).card := by omega
    exact Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp this)
  apply nineClause_fullCircuit_uses_at_least_two_questions
    (restrictQueryToIntegerSupport query c)
  · rw [Fintype.card_coe]
    exact hcard
  · exact primitiveKernelCircuit_restricted_isFullRationalCircuit
      query c hc

/-- At most one page of a nine-clause primitive integer circuit is nonternary. -/
theorem nineClause_primitiveIncidenceCircuit_has_at_most_one_nonternary_player
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (hcard : (integerSupport c).card = 9) :
    ∃ exceptional : Fin 4, ∀ player ≠ exceptional,
      usedQuestionsCard
        (restrictQueryToIntegerSupport query c) player = 3 := by
  letI : Nonempty ↥(integerSupport c) := by
    have : 0 < (integerSupport c).card := by omega
    exact Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp this)
  apply nineClause_fullCircuit_has_at_most_one_nonternary_player
    (restrictQueryToIntegerSupport query c)
  · rw [Fintype.card_coe]
    exact hcard
  · exact primitiveKernelCircuit_restricted_isFullRationalCircuit
      query c hc

/-- At least three pages of a nine-clause primitive integer circuit are ternary. -/
theorem nineClause_primitiveIncidenceCircuit_has_three_ternary_players
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (c : E → ℤ)
    (hc :
      IsPrimitiveKernelCircuit
        (incidenceRelationHom query) c)
    (hcard : (integerSupport c).card = 9) :
    3 ≤
      (ternaryPlayers
        (restrictQueryToIntegerSupport query c)).card := by
  letI : Nonempty ↥(integerSupport c) := by
    have : 0 < (integerSupport c).card := by omega
    exact Finset.nonempty_coe_sort.mpr (Finset.card_pos.mp this)
  apply nineClause_fullCircuit_has_three_ternary_players
    (restrictQueryToIntegerSupport query c)
  · rw [Fintype.card_coe]
    exact hcard
  · exact primitiveKernelCircuit_restricted_isFullRationalCircuit
      query c hc

end

end XORGame
end QIT

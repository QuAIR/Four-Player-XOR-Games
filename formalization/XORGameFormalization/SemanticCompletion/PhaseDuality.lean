/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.MERPStrategy
public import XORGameFormalization.SemanticCompletion.GameNormalization
public import XORGameFormalization.Spaces
public import Mathlib.Algebra.Category.Grp.Injective
public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Tactic

/-!
# Duality between MERP parity and physical MERP phase assignments

This module proves that the finite integer parity condition
`IsMERPPerfectParity` on the normalized clause support is equivalent to the
existence of a phase assignment satisfying all signed clause equations.
The hard direction interprets a satisfying phase assignment as an additive
character of the free abelian group on player-question pairs.  The clause
sign vector defines a character on the incidence image, which extends to the
whole free abelian group because the circle group is divisible
(`Module.Baer.of_divisible` + `extension_property_addMonoidHom`).
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

namespace FiniteFourPlayerXORGame

variable (G : FiniteFourPlayerXORGame Question)

/-- The integer value of a `ZMod 2` sign, as `0` or `1`. -/
def zmodVal (x : ZMod 2) : ℤ := (x.val : ℤ)

theorem zmodVal_cast (x : ZMod 2) : (zmodVal x : ZMod 2) = x := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one x with hx | hx
  · simp [zmodVal, hx]
  · simp [zmodVal, hx]

/-- The MERP parity condition on the normalized no-conflict support. -/
def IsMERPPerfectParityOnSupport (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) : Prop :=
  IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)

/-- The free abelian basis of phase variables: one pair per player/question. -/
abbrev PhaseBasis (Question : Type uQ) := Fin 4 × Question

/-- The integer incidence homomorphism from clause indices to player-question
coordinates. -/
def incidenceAddMonoidHom (G : FiniteFourPlayerXORGame Question) :
    (G.ReducedClauseId → ℤ) →+ (PhaseBasis Question → ℤ) where
  toFun y pq := ∑ c : G.ReducedClauseId, incidence G.reducedQuery c pq * y c
  map_zero' := by
    ext pq
    simp
  map_add' := by
    intro y z
    ext pq
    simp [Finset.sum_add_distrib, mul_add]

/-- The sign character of clause-index vectors into the unit circle. -/
def signSum (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    (G.ReducedClauseId → ℤ) →+ UnitAddCircle where
  toFun y := (((∑ c : G.ReducedClauseId,
      zmodVal (G.reducedSign hconflict c) * y c : ℤ) : ℝ) / (2 : ℝ) : UnitAddCircle)
  map_zero' := by simp
  map_add' := by
    intro y z
    apply congrArg QuotientAddGroup.mk
    simp [Finset.sum_add_distrib, mul_add]
    ring

@[simp]
theorem signSum_eval (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (y : G.ReducedClauseId → ℤ) :
    G.signSum hconflict y =
      (((∑ c : G.ReducedClauseId,
        zmodVal (G.reducedSign hconflict c) * y c : ℤ) : ℝ) / (2 : ℝ) : UnitAddCircle) :=
  rfl

private theorem parity_even_of_isMERPPerfectParity (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict))
    {y : G.ReducedClauseId → ℤ} (hy : IsIntegerRelation G.reducedQuery y) :
    parityPairing (G.reducedSign hconflict) (relationParity y) = 0 := by
  by_contra hne
  have hone : parityPairing (G.reducedSign hconflict) (relationParity y) = 1 := by
    rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one
        (parityPairing (G.reducedSign hconflict) (relationParity y)) with hz | hz
    · exact False.elim (hne hz)
    · exact hz
  exact (isMERPPerfectParity_iff_not_hasPREF
    G.reducedQuery (G.reducedSign hconflict)).mp hmerp ⟨y, hy, hone⟩

private theorem signSum_zero_of_integerRelation (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict))
    {y : G.ReducedClauseId → ℤ} (hy : IsIntegerRelation G.reducedQuery y) :
    G.signSum hconflict y = 0 := by
  have hpar := G.parity_even_of_isMERPPerfectParity hconflict hmerp hy
  have hSmod : ((∑ c : G.ReducedClauseId,
      zmodVal (G.reducedSign hconflict c) * y c : ℤ) : ZMod 2) = 0 := by
    calc
      ((∑ c : G.ReducedClauseId,
          zmodVal (G.reducedSign hconflict c) * y c : ℤ) : ZMod 2)
          = ∑ c : G.ReducedClauseId,
              ((zmodVal (G.reducedSign hconflict c) * y c : ℤ) : ZMod 2) := by
              simp
      _ = ∑ c : G.ReducedClauseId,
              (G.reducedSign hconflict c : ZMod 2) * (y c : ZMod 2) := by
              apply Finset.sum_congr rfl
              intro c hc
              simp [Int.cast_mul, zmodVal_cast]
      _ = parityPairing (G.reducedSign hconflict) (relationParity y) := rfl
      _ = 0 := hpar
  have hSdvd : ∃ k : ℤ, (∑ c : G.ReducedClauseId,
      zmodVal (G.reducedSign hconflict c) * y c : ℤ) = 2 * k := by
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (∑ c : G.ReducedClauseId,
        zmodVal (G.reducedSign hconflict c) * y c : ℤ) 2).mp hSmod
  rcases hSdvd with ⟨k, hk⟩
  rw [signSum_eval, hk]
  have h2k : (((2 * k : ℤ) : ℝ) / (2 : ℝ) : ℝ) = (k : ℝ) := by
    rw [Int.cast_mul]
    ring
  rw [h2k]
  simp

private theorem signSum_eq_of_incidence_eq (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict))
    {y z : G.ReducedClauseId → ℤ}
    (h : G.incidenceAddMonoidHom y = G.incidenceAddMonoidHom z) :
    G.signSum hconflict y = G.signSum hconflict z := by
  have hrel : IsIntegerRelation G.reducedQuery (y - z) := by
    intro pq
    have hpq := congrFun h pq
    calc
      (∑ c : G.ReducedClauseId,
          incidence G.reducedQuery c pq * (y - z) c)
          = (∑ c : G.ReducedClauseId,
              incidence G.reducedQuery c pq * y c) -
            (∑ c : G.ReducedClauseId,
              incidence G.reducedQuery c pq * z c) := by
              simp [sub_eq_add_neg, Finset.sum_add_distrib, mul_add, mul_neg, add_comm]
      _ = 0 := sub_eq_zero.mpr hpq
  have hzero := G.signSum_zero_of_integerRelation hconflict hmerp hrel
  have hsub : G.signSum hconflict y - G.signSum hconflict z = 0 := by
    rw [← AddMonoidHom.map_sub]
    exact hzero
  exact sub_eq_zero.mp hsub

private def rangeHom (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    (G.incidenceAddMonoidHom).range →+ UnitAddCircle where
  toFun x := G.signSum hconflict
    (Classical.choose (AddMonoidHom.mem_range.mp x.2))
  map_zero' := by
    let z := Classical.choose
      (AddMonoidHom.mem_range.mp (AddSubgroup.zero_mem (G.incidenceAddMonoidHom).range))
    have hz : G.incidenceAddMonoidHom z = 0 := Classical.choose_spec
      (AddMonoidHom.mem_range.mp (AddSubgroup.zero_mem (G.incidenceAddMonoidHom).range))
    have hrel : IsIntegerRelation G.reducedQuery z := by
      intro pq
      exact congrFun hz pq
    exact G.signSum_zero_of_integerRelation hconflict hmerp hrel
  map_add' := by
    intro x y
    let zx := Classical.choose (AddMonoidHom.mem_range.mp x.2)
    let zy := Classical.choose (AddMonoidHom.mem_range.mp y.2)
    let zxy := Classical.choose (AddMonoidHom.mem_range.mp
      (AddSubgroup.add_mem (G.incidenceAddMonoidHom).range x.2 y.2))
    have hx : G.incidenceAddMonoidHom zx = x.1 := Classical.choose_spec
      (AddMonoidHom.mem_range.mp x.2)
    have hy : G.incidenceAddMonoidHom zy = y.1 := Classical.choose_spec
      (AddMonoidHom.mem_range.mp y.2)
    have hxy : G.incidenceAddMonoidHom zxy = x.1 + y.1 := Classical.choose_spec
      (AddMonoidHom.mem_range.mp (AddSubgroup.add_mem (G.incidenceAddMonoidHom).range x.2 y.2))
    have hwd : G.signSum hconflict zxy = G.signSum hconflict (zx + zy) :=
      G.signSum_eq_of_incidence_eq hconflict hmerp (by
        rw [hxy, AddMonoidHom.map_add, hx, hy])
    calc
      G.signSum hconflict zxy = G.signSum hconflict (zx + zy) := hwd
      _ = G.signSum hconflict zx + G.signSum hconflict zy := by
        exact AddMonoidHom.map_add (G.signSum hconflict) zx zy

private def extendedChar (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    (PhaseBasis Question → ℤ) →+ UnitAddCircle :=
  Classical.choose
    ((Module.Baer.of_divisible (A := UnitAddCircle)).extension_property_addMonoidHom
      (G.incidenceAddMonoidHom).range.subtype (Subtype.coe_injective)
      (G.rangeHom hconflict hmerp))

private theorem extendedChar_spec (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    (G.extendedChar hconflict hmerp).comp (G.incidenceAddMonoidHom).range.subtype =
      G.rangeHom hconflict hmerp := by
  unfold extendedChar
  exact Classical.choose_spec
    ((Module.Baer.of_divisible (A := UnitAddCircle)).extension_property_addMonoidHom
      (G.incidenceAddMonoidHom).range.subtype (Subtype.coe_injective)
      (G.rangeHom hconflict hmerp))

private theorem extendedChar_eval (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict))
    (y : G.ReducedClauseId → ℤ) :
    G.extendedChar hconflict hmerp (G.incidenceAddMonoidHom y) =
      G.signSum hconflict y := by
  have hcomp := G.extendedChar_spec hconflict hmerp
  have hm : G.incidenceAddMonoidHom y ∈ (G.incidenceAddMonoidHom).range :=
    AddMonoidHom.mem_range.mpr ⟨y, rfl⟩
  have h := DFunLike.congr_fun hcomp ⟨G.incidenceAddMonoidHom y, hm⟩
  let z := Classical.choose (AddMonoidHom.mem_range.mp hm)
  have hz : G.incidenceAddMonoidHom z = G.incidenceAddMonoidHom y :=
    Classical.choose_spec (AddMonoidHom.mem_range.mp hm)
  have hz' : G.signSum hconflict z = G.signSum hconflict y :=
    G.signSum_eq_of_incidence_eq (y := z) (z := y) hconflict hmerp hz
  exact h.trans hz'

private def phaseChar (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    AddChar (PhaseBasis Question → ℤ) Circle :=
  AddCircle.toCircle_addChar.compAddMonoidHom (G.extendedChar hconflict hmerp)

private theorem single_sum_eq_incidence (G : FiniteFourPlayerXORGame Question)
    (c : G.ReducedClauseId) :
    (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
      (p, G.reducedQuery c p) (1 : ℤ)) =
      G.incidenceAddMonoidHom (Pi.single (M := fun _ : G.ReducedClauseId => ℤ)
        c (1 : ℤ)) := by
  ext pq
  rcases pq with ⟨p', q'⟩
  simp [incidenceAddMonoidHom, Pi.single, Function.update_apply]
  by_cases hq : G.reducedQuery c p' = q'
  · have hset : ({x : Fin 4 | p' = x ∧ q' = G.reducedQuery c x} : Finset (Fin 4)) =
        {p'} := by
        ext x
        constructor
        · intro hx
          simp at hx
          rcases hx with ⟨hx1, hx2⟩
          simp [hx1]
        · intro hx
          have hx' : x = p' := Finset.eq_of_mem_singleton hx
          simp [hx', hq]
    rw [hset]
    simp [hq]
  · have hset : ({x : Fin 4 | p' = x ∧ q' = G.reducedQuery c x} : Finset (Fin 4)) =
        ∅ := by
        ext x
        constructor
        · intro hx
          simp at hx
          rcases hx with ⟨hx1, hx2⟩
          exact False.elim (hq (by rw [hx1]; exact hx2.symm))
        · intro hx
          simp at hx
    rw [hset]
    simp [hq]

private theorem phaseChar_clause (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict))
    (c : G.ReducedClauseId) :
    (∏ p : Fin 4,
      G.phaseChar hconflict hmerp (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ))) =
      binaryXORCirclePhase (G.reducedSign hconflict c) := by
  let χ := G.phaseChar hconflict hmerp
  have hχ : χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
      (p, G.reducedQuery c p) (1 : ℤ)) =
      ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ)) := by
    have hmap := map_prod χ.toMonoidHom
      (fun p : Fin 4 => Multiplicative.ofAdd
        (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ))) Finset.univ
    have hprod : (∏ p ∈ Finset.univ, Multiplicative.ofAdd
        (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ))) =
        Multiplicative.ofAdd (∑ p : Fin 4,
          Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := by
      simpa using (map_prod (Multiplicative.ofAddHom)
        (fun p : Fin 4 => Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ)) Finset.univ).symm
    calc
      χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ))
          = χ.toMonoidHom (Multiplicative.ofAdd (∑ p : Fin 4,
              Pi.single (M := fun _ : Fin 4 × Question => ℤ)
                (p, G.reducedQuery c p) (1 : ℤ))) := by
              rw [AddChar.toMonoidHom_apply]
              simp
      _ = χ.toMonoidHom (∏ p ∈ Finset.univ, Multiplicative.ofAdd
              (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
                (p, G.reducedQuery c p) (1 : ℤ))) := by rw [← hprod]
      _ = ∏ p ∈ Finset.univ, χ.toMonoidHom (Multiplicative.ofAdd
              (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
                (p, G.reducedQuery c p) (1 : ℤ))) := hmap
      _ = ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
              (p, G.reducedQuery c p) (1 : ℤ)) := by
              simp_rw [AddChar.toMonoidHom_apply]
              simp
  have hsum := G.single_sum_eq_incidence c
  have heval := G.extendedChar_eval hconflict hmerp
    (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))
  have hsign : G.signSum hconflict
      (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)) =
      ZMod.toAddCircle (G.reducedSign hconflict c) := by
    have hsumc : (∑ d : G.ReducedClauseId,
        zmodVal (G.reducedSign hconflict d) *
          (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ) d) : ℤ) =
        zmodVal (G.reducedSign hconflict c) := by
      calc
        (∑ d : G.ReducedClauseId,
            zmodVal (G.reducedSign hconflict d) *
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ) d) : ℤ)
            = zmodVal (G.reducedSign hconflict c) *
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ) c) := by
              exact Finset.sum_eq_single c (by
                intro b hb hne
                simp [hne]) (by intro hc; simp at hc)
        _ = zmodVal (G.reducedSign hconflict c) := by simp
    rw [signSum_eval, hsumc]
    simpa [zmodVal_cast] using
      (ZMod.toAddCircle_intCast (N := 2) (j := zmodVal (G.reducedSign hconflict c)))
  calc
    (∏ p : Fin 4,
        G.phaseChar hconflict hmerp (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ)))
        = ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := by
            rfl
    _ = χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := hχ.symm
    _ = χ (G.incidenceAddMonoidHom (Pi.single (M := fun _ : G.ReducedClauseId => ℤ)
            c (1 : ℤ))) := by rw [hsum]
    _ = AddCircle.toCircle (G.signSum hconflict
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) := by
            change AddCircle.toCircle (G.extendedChar hconflict hmerp
              (G.incidenceAddMonoidHom
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) =
              AddCircle.toCircle (G.signSum hconflict
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))
            rw [heval]
    _ = AddCircle.toCircle (ZMod.toAddCircle (G.reducedSign hconflict c)) := by rw [hsign]
    _ = binaryXORCirclePhase (G.reducedSign hconflict c) := by
            rfl

private def merpPhaseOfParity (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    MERPPhaseAssignment Question :=
  fun p q => G.phaseChar hconflict hmerp
    (Pi.single (M := fun _ : Fin 4 × Question => ℤ) (p, q) (1 : ℤ))

private theorem satisfies_phase_of_parity (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict)) :
    SatisfiesMERPPhaseAssignment G (G.merpPhaseOfParity hconflict hmerp) := by
  intro signedClause hsigned
  rcases signedClause with ⟨query, b⟩
  -- The signed clause lies in the reduced support: find the reduced clause index.
  let hred : G.ReducedClauseId := ⟨query, b, (G.mem_support_iff (query, b)).mp hsigned⟩
  have hb : b = G.reducedSign hconflict hred :=
    G.reducedSign_unique hconflict hred b ((G.mem_support_iff (query, b)).mp hsigned)
  change (∏ p : Fin 4, G.merpPhaseOfParity hconflict hmerp p (query p)) =
    binaryXORCirclePhase b
  rw [hb]
  simpa [merpPhaseOfParity] using G.phaseChar_clause hconflict hmerp hred

private theorem parity_implies_hasPerfectMERPStrategy (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hmerp : G.IsMERPPerfectParityOnSupport hconflict) :
    HasPerfectMERPStrategy G := by
  unfold IsMERPPerfectParityOnSupport at hmerp
  refine ⟨G.merpPhaseOfParity hconflict hmerp, ?_⟩
  exact G.satisfies_phase_of_parity hconflict hmerp

/-- The underlying function of the additive character of a phase
assignment. -/
private def phaseCharFun (phase : MERPPhaseAssignment Question) :
    (PhaseBasis Question → ℤ) → Circle :=
  fun x => ∏ pq : PhaseBasis Question, phase pq.1 pq.2 ^ (x pq : ℤ)

/-- The additive character of a phase assignment. -/
private def phaseCharOfAssignment (phase : MERPPhaseAssignment Question) :
    AddChar (PhaseBasis Question → ℤ) Circle where
  toFun := phaseCharFun phase
  map_zero_eq_one' := by
    change phaseCharFun phase 0 = 1
    simp [phaseCharFun]
  map_add_eq_mul' := by
    intro x y
    change phaseCharFun phase (x + y) = phaseCharFun phase x * phaseCharFun phase y
    unfold phaseCharFun
    calc
      (∏ pq : PhaseBasis Question, phase pq.1 pq.2 ^ ((x + y) pq : ℤ))
          = (∏ pq : PhaseBasis Question,
              phase pq.1 pq.2 ^ (x pq : ℤ) * phase pq.1 pq.2 ^ (y pq : ℤ)) := by
              apply Finset.prod_congr rfl
              intro pq hpq
              change phase pq.1 pq.2 ^ (x pq + y pq) =
                phase pq.1 pq.2 ^ (x pq) * phase pq.1 pq.2 ^ (y pq)
              rw [zpow_add]
      _ = (∏ pq : PhaseBasis Question, phase pq.1 pq.2 ^ (x pq : ℤ)) *
          (∏ pq : PhaseBasis Question, phase pq.1 pq.2 ^ (y pq : ℤ)) := by
              rw [Finset.prod_mul_distrib]

private theorem addChar_sum_single {χ : AddChar (PhaseBasis Question → ℤ) Circle}
    (G : FiniteFourPlayerXORGame Question) (c : G.ReducedClauseId) :
    χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ)) =
      ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ)) := by
  have hmap := map_prod χ.toMonoidHom
    (fun p : Fin 4 => Multiplicative.ofAdd
      (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ))) Finset.univ
  have hprod : (∏ p ∈ Finset.univ, Multiplicative.ofAdd
      (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ))) =
      Multiplicative.ofAdd (∑ p : Fin 4,
        Pi.single (M := fun _ : Fin 4 × Question => ℤ)
          (p, G.reducedQuery c p) (1 : ℤ)) := by
    simpa using (map_prod (Multiplicative.ofAddHom)
      (fun p : Fin 4 => Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ)) Finset.univ).symm
  calc
    χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ))
        = χ.toMonoidHom (Multiplicative.ofAdd (∑ p : Fin 4,
            Pi.single (M := fun _ : Fin 4 × Question => ℤ)
              (p, G.reducedQuery c p) (1 : ℤ))) := by
            rw [AddChar.toMonoidHom_apply]
            simp
    _ = χ.toMonoidHom (∏ p ∈ Finset.univ, Multiplicative.ofAdd
            (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
              (p, G.reducedQuery c p) (1 : ℤ))) := by rw [← hprod]
    _ = ∏ p ∈ Finset.univ, χ.toMonoidHom (Multiplicative.ofAdd
            (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
              (p, G.reducedQuery c p) (1 : ℤ))) := hmap
    _ = ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := by
            simp_rw [AddChar.toMonoidHom_apply]
            simp

private theorem phaseCharOfAssignment_single (phase : MERPPhaseAssignment Question)
    (p : Fin 4) (q : Question) :
    phaseCharOfAssignment phase (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, q) (1 : ℤ)) = phase p q := by
  simp [phaseCharOfAssignment, phaseCharFun, Pi.single, Function.update_apply]

private theorem phaseCharOfAssignment_clause (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (phase : MERPPhaseAssignment Question)
    (hclause : ∀ c : G.ReducedClauseId,
      (∏ p : Fin 4, phase p (G.reducedQuery c p)) =
        binaryXORCirclePhase (G.reducedSign hconflict c))
    (c : G.ReducedClauseId) :
    phaseCharOfAssignment phase (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) =
      binaryXORCirclePhase (G.reducedSign hconflict c) := by
  let χ := phaseCharOfAssignment phase
  have hχ := G.addChar_sum_single (χ := χ) c
  have hsum := G.single_sum_eq_incidence c
  have hsingle : ∀ p : Fin 4,
      χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
        (p, G.reducedQuery c p) (1 : ℤ)) = phase p (G.reducedQuery c p) := by
    intro p
    simpa [χ] using phaseCharOfAssignment_single phase p (G.reducedQuery c p)
  calc
    χ (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))
        = χ (∑ p : Fin 4, Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := by rw [hsum]
    _ = ∏ p : Fin 4, χ (Pi.single (M := fun _ : Fin 4 × Question => ℤ)
            (p, G.reducedQuery c p) (1 : ℤ)) := hχ
    _ = ∏ p : Fin 4, phase p (G.reducedQuery c p) := by
            apply Finset.prod_congr rfl
            intro p hp
            exact hsingle p
    _ = binaryXORCirclePhase (G.reducedSign hconflict c) := hclause c

private theorem sum_smul_single_eq_self (G : FiniteFourPlayerXORGame Question)
    (y : G.ReducedClauseId → ℤ) :
    (∑ c : G.ReducedClauseId, (y c) • Pi.single (M := fun _ : G.ReducedClauseId => ℤ)
        c (1 : ℤ)) = y := by
  ext c
  rw [Finset.sum_apply]
  simp [Pi.single, Function.update_apply]

private theorem incidenceAddMonoidHom_sum_smul (G : FiniteFourPlayerXORGame Question)
    (y : G.ReducedClauseId → ℤ) :
    G.incidenceAddMonoidHom y =
      ∑ c : G.ReducedClauseId, (y c) • G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)) := by
  calc
    G.incidenceAddMonoidHom y
        = G.incidenceAddMonoidHom (∑ c : G.ReducedClauseId,
            (y c) • Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)) := by
            rw [G.sum_smul_single_eq_self y]
    _ = ∑ c : G.ReducedClauseId, G.incidenceAddMonoidHom
            ((y c) • Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)) := by
            rw [map_sum]
    _ = ∑ c : G.ReducedClauseId, (y c) • G.incidenceAddMonoidHom
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)) := by
            apply Finset.sum_congr rfl
            intro c hc
            exact AddMonoidHom.map_zsmul (G.incidenceAddMonoidHom) (y c)
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))

private theorem binaryXORCirclePhase_zpow (b : ZMod 2) (n : ℤ) :
    binaryXORCirclePhase b ^ n = binaryXORCirclePhase (b * (n : ZMod 2)) := by
  have h := (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom.map_zpow
    (Multiplicative.ofAdd b) n
  calc
    binaryXORCirclePhase b ^ n
        = (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
            (Multiplicative.ofAdd b) ^ n := by simp [binaryXORCirclePhase]
    _ = (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
            ((Multiplicative.ofAdd b) ^ n) := h.symm
    _ = (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
            (Multiplicative.ofAdd (n • b)) := by rfl
    _ = (ZMod.toCircle : AddChar (ZMod 2) Circle) (n • b) := by
            rw [AddChar.toMonoidHom_apply]
            simp
    _ = binaryXORCirclePhase (b * (n : ZMod 2)) := by
            rw [zsmul_eq_mul, mul_comm]
            rfl

private theorem hasPerfectMERPStrategy_implies_isMERPPerfectParityOnSupport
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hphase : HasPerfectMERPStrategy G) :
    G.IsMERPPerfectParityOnSupport hconflict := by
  rcases hphase with ⟨phase, hphase⟩
  unfold IsMERPPerfectParityOnSupport
  rw [isMERPPerfectParity_iff_not_hasPREF]
  intro hpref
  rcases hpref with ⟨y, hyrel, hyodd⟩
  let χ := phaseCharOfAssignment phase
  have hclause : ∀ c : G.ReducedClauseId,
      (∏ p : Fin 4, phase p (G.reducedQuery c p)) =
        binaryXORCirclePhase (G.reducedSign hconflict c) := by
    intro c
    exact hphase (G.reducedQuery c, G.reducedSign hconflict c)
      (G.reducedSignedClause_mem_support hconflict c)
  have hcχ : ∀ c : G.ReducedClauseId,
      χ (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) =
        binaryXORCirclePhase (G.reducedSign hconflict c) := by
    intro c
    simpa [χ] using G.phaseCharOfAssignment_clause hconflict phase hclause c
  have hAy : G.incidenceAddMonoidHom y = 0 := by
    ext pq
    exact hyrel pq
  have hχAy : χ (G.incidenceAddMonoidHom y) = 1 := by
    rw [hAy]
    simp [χ]
  have hprod : χ (G.incidenceAddMonoidHom y) =
      ∏ c : G.ReducedClauseId, (χ (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c) := by
    rw [G.incidenceAddMonoidHom_sum_smul y]
    -- χ (∑ c, (y c) • A e_c) = ∏ c, (χ (A e_c)) ^ (y c)
    have hsumprod : χ (∑ c : G.ReducedClauseId,
        (y c) • G.incidenceAddMonoidHom
          (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) =
        ∏ c : G.ReducedClauseId, χ ((y c) • G.incidenceAddMonoidHom
          (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) := by
      have hmap := map_prod χ.toMonoidHom
        (fun c : G.ReducedClauseId => Multiplicative.ofAdd
          ((y c) • G.incidenceAddMonoidHom
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) Finset.univ
      have hprod : (∏ c ∈ Finset.univ, Multiplicative.ofAdd
          ((y c) • G.incidenceAddMonoidHom
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) =
          Multiplicative.ofAdd (∑ c : G.ReducedClauseId,
            (y c) • G.incidenceAddMonoidHom
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) := by
        simpa using (map_prod (Multiplicative.ofAddHom)
          (fun c : G.ReducedClauseId => (y c) • G.incidenceAddMonoidHom
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) Finset.univ).symm
      calc
        χ (∑ c : G.ReducedClauseId,
            (y c) • G.incidenceAddMonoidHom
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))
            = χ.toMonoidHom (Multiplicative.ofAdd (∑ c : G.ReducedClauseId,
                (y c) • G.incidenceAddMonoidHom
                  (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) := by
                rw [AddChar.toMonoidHom_apply]
                simp
        _ = χ.toMonoidHom (∏ c ∈ Finset.univ, Multiplicative.ofAdd
                ((y c) • G.incidenceAddMonoidHom
                  (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) := by
                rw [← hprod]
        _ = ∏ c ∈ Finset.univ, χ.toMonoidHom (Multiplicative.ofAdd
                ((y c) • G.incidenceAddMonoidHom
                  (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) := hmap
        _ = ∏ c : G.ReducedClauseId, χ ((y c) • G.incidenceAddMonoidHom
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ))) := by
                simp_rw [AddChar.toMonoidHom_apply]
                simp
    rw [hsumprod]
    apply Finset.prod_congr rfl
    intro c hc
    have hpow := (χ.toMonoidHom.map_zpow
      (Multiplicative.ofAdd (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) (y c))
    calc
      χ ((y c) • G.incidenceAddMonoidHom
          (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))
          = χ.toMonoidHom (Multiplicative.ofAdd ((y c) •
              G.incidenceAddMonoidHom
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) := by
              rw [AddChar.toMonoidHom_apply]
              simp
      _ = χ.toMonoidHom ((Multiplicative.ofAdd (G.incidenceAddMonoidHom
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c)) := by rfl
      _ = (χ (G.incidenceAddMonoidHom
              (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c) := hpow
  have hprod2 : (∏ c : G.ReducedClauseId,
      (χ (G.incidenceAddMonoidHom
        (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c)) =
      binaryXORCirclePhase (parityPairing (G.reducedSign hconflict) (relationParity y)) := by
    calc
      (∏ c : G.ReducedClauseId,
          (χ (G.incidenceAddMonoidHom
            (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c))
          = ∏ c : G.ReducedClauseId,
              (binaryXORCirclePhase (G.reducedSign hconflict c)) ^ (y c) := by
              apply Finset.prod_congr rfl
              intro c hc
              rw [hcχ c]
      _ = ∏ c : G.ReducedClauseId,
              binaryXORCirclePhase (G.reducedSign hconflict c * (y c : ZMod 2)) := by
              apply Finset.prod_congr rfl
              intro c hc
              exact binaryXORCirclePhase_zpow (G.reducedSign hconflict c) (y c)
      _ = binaryXORCirclePhase (∑ c : G.ReducedClauseId,
              G.reducedSign hconflict c * (y c : ZMod 2)) := by
              have hmap := map_prod (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
                (fun c : G.ReducedClauseId => Multiplicative.ofAdd
                  (G.reducedSign hconflict c * (y c : ZMod 2))) Finset.univ
              have hprod' : (∏ c ∈ Finset.univ, Multiplicative.ofAdd
                  (G.reducedSign hconflict c * (y c : ZMod 2))) =
                  Multiplicative.ofAdd (∑ c : G.ReducedClauseId,
                    G.reducedSign hconflict c * (y c : ZMod 2)) := by
                simpa using (map_prod (Multiplicative.ofAddHom)
                  (fun c : G.ReducedClauseId =>
                    G.reducedSign hconflict c * (y c : ZMod 2)) Finset.univ).symm
              calc
                (∏ c : G.ReducedClauseId,
                    binaryXORCirclePhase
                      (G.reducedSign hconflict c * (y c : ZMod 2)))
                    = ∏ c ∈ Finset.univ, (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
                        (Multiplicative.ofAdd
                          (G.reducedSign hconflict c * (y c : ZMod 2))) := by
                        apply Finset.prod_congr rfl
                        intro c hc
                        rw [AddChar.toMonoidHom_apply]
                        simp [binaryXORCirclePhase]
                _ = (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom
                        (∏ c ∈ Finset.univ, Multiplicative.ofAdd
                          (G.reducedSign hconflict c * (y c : ZMod 2))) := hmap.symm
                _ = (ZMod.toCircle : AddChar (ZMod 2) Circle).toMonoidHom (Multiplicative.ofAdd
                        (∑ c : G.ReducedClauseId,
                          G.reducedSign hconflict c * (y c : ZMod 2))) := by rw [hprod']
                _ = binaryXORCirclePhase (∑ c : G.ReducedClauseId,
                        G.reducedSign hconflict c * (y c : ZMod 2)) := by
                        rw [AddChar.toMonoidHom_apply]
                        simp [binaryXORCirclePhase]
      _ = binaryXORCirclePhase (parityPairing (G.reducedSign hconflict) (relationParity y)) := rfl
  have hχAy1 : (1 : Circle) =
      binaryXORCirclePhase (parityPairing (G.reducedSign hconflict) (relationParity y)) := by
    calc
      (1 : Circle) = χ (G.incidenceAddMonoidHom y) := hχAy.symm
      _ = ∏ c : G.ReducedClauseId,
              (χ (G.incidenceAddMonoidHom
                (Pi.single (M := fun _ : G.ReducedClauseId => ℤ) c (1 : ℤ)))) ^ (y c) := hprod
      _ = binaryXORCirclePhase (parityPairing (G.reducedSign hconflict) (relationParity y)) := hprod2
  have hone : (1 : Circle) = binaryXORCirclePhase (1 : ZMod 2) := by
    rw [hyodd] at hχAy1
    exact hχAy1
  have hne : (1 : Circle) ≠ binaryXORCirclePhase (1 : ZMod 2) := by
    simpa [binaryXORCirclePhase_zero] using binaryXORCirclePhase_zero_ne_one
  exact hne hone

/-- The MERP parity condition on the normalized support is equivalent to the
existence of a physical MERP phase assignment. -/
theorem isMERPPerfectParityOnSupport_iff_hasPerfectMERPStrategy
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    G.IsMERPPerfectParityOnSupport hconflict ↔ HasPerfectMERPStrategy G := by
  constructor
  · exact G.parity_implies_hasPerfectMERPStrategy hconflict
  · exact G.hasPerfectMERPStrategy_implies_isMERPPerfectParityOnSupport hconflict

/-- A concrete game with one question and two opposite-sign clauses: target
conflict excludes any perfect MERP strategy. -/
noncomputable def conflictGame : FiniteFourPlayerXORGame (Fin 1) :=
  FiniteFourPlayerXORGame.ofIndexed
    (ClauseId := Fin 2)
    (query := fun _ _ => (0 : Fin 1))
    (sign := fun c => (c : ZMod 2))
    (weight := fun _ => (1 / 2 : ℝ))
    (by intro c; positivity)
    (by norm_num [Fin.sum_univ_two])

private theorem conflictGame_weight_pos (b : ZMod 2) :
    0 < conflictGame.weight ((fun _ : Fin 4 => (0 : Fin 1)), b) := by
  have hw : conflictGame.weight ((fun _ : Fin 4 => (0 : Fin 1)), b) =
      (∑ c : Fin 2,
        if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
            (c : ZMod 2) = b then (1 / 2 : ℝ) else 0) := rfl
  have hsum : (∑ c : Fin 2,
      if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
          (c : ZMod 2) = b then (1 / 2 : ℝ) else 0) = 1 / 2 := by
    rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
    · subst b
      calc
        (∑ c : Fin 2,
            if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
                (c : ZMod 2) = (0 : ZMod 2) then (1 / 2 : ℝ) else 0)
            = (if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
                  ((0 : Fin 2) : ZMod 2) = (0 : ZMod 2) then (1 / 2 : ℝ) else 0) := by
              exact Finset.sum_eq_single (0 : Fin 2) (by
                intro c hc hne
                fin_cases c <;> simp at hne ⊢) (by intro hmem; simp at hmem)
        _ = 1 / 2 := by simp
    · subst b
      calc
        (∑ c : Fin 2,
            if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
                (c : ZMod 2) = (1 : ZMod 2) then (1 / 2 : ℝ) else 0)
            = (if (fun _ : Fin 4 => (0 : Fin 1)) = (fun _ : Fin 4 => (0 : Fin 1)) ∧
                  ((1 : Fin 2) : ZMod 2) = (1 : ZMod 2) then (1 / 2 : ℝ) else 0) := by
              exact Finset.sum_eq_single (1 : Fin 2) (by
                intro c hc hne
                fin_cases c <;> simp at hne ⊢) (by intro hmem; simp at hmem)
        _ = 1 / 2 := by simp
  rw [hw, hsum]
  norm_num

example : conflictGame.HasConflictingTargets := by
  refine ⟨(fun _ : Fin 4 => (0 : Fin 1)), ?_, ?_⟩
  · exact conflictGame_weight_pos 0
  · exact conflictGame_weight_pos 1

example : ¬ HasPerfectMERPStrategy conflictGame := by
  intro hphase
  rcases hphase with ⟨phase, hphase⟩
  have h0 : (∏ p : Fin 4, phase p (0 : Fin 1)) = binaryXORCirclePhase (0 : ZMod 2) := by
    exact hphase ((fun _ : Fin 4 => (0 : Fin 1)), (0 : ZMod 2)) (by
      rw [FiniteFourPlayerXORGame.mem_support_iff]
      exact conflictGame_weight_pos 0)
  have h1 : (∏ p : Fin 4, phase p (0 : Fin 1)) = binaryXORCirclePhase (1 : ZMod 2) := by
    exact hphase ((fun _ : Fin 4 => (0 : Fin 1)), (1 : ZMod 2)) (by
      rw [FiniteFourPlayerXORGame.mem_support_iff]
      exact conflictGame_weight_pos 1)
  have heq : binaryXORCirclePhase (0 : ZMod 2) = binaryXORCirclePhase (1 : ZMod 2) := by
    rw [← h0, h1]
  exact binaryXORCirclePhase_zero_ne_one heq

end FiniteFourPlayerXORGame

end

end XORGame
end QIT

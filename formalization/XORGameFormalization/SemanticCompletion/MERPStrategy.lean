/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.GeneralObservableStrategy
public import XORGameFormalization.ObservableStrategy
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.Matrix
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Tactic

/-!
# Physical MERP strategies

This module formalizes the explicit four-qubit GHZ/equatorial realization of
MERP phase assignments.  A MERP strategy is a unit phase per player/question,
the four-qubit GHZ state, and the corresponding equatorial binary observables.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

/-- The binary XOR phase with values in the unit complex circle. -/
noncomputable def binaryXORCirclePhase (sign : ZMod 2) : Circle :=
  ZMod.toCircle sign

@[simp]
theorem binaryXORCirclePhase_zero :
    binaryXORCirclePhase (0 : ZMod 2) = 1 := by
  simpa [binaryXORCirclePhase] using
    (ZMod.toCircle : AddChar (ZMod 2) Circle).map_zero_eq_one

theorem binaryXORCirclePhase_add (a b : ZMod 2) :
    binaryXORCirclePhase (a + b) =
      binaryXORCirclePhase a * binaryXORCirclePhase b := by
  simpa [binaryXORCirclePhase] using
    (ZMod.toCircle : AddChar (ZMod 2) Circle).map_add_eq_mul a b

@[simp]
theorem binaryXORCirclePhase_one :
    binaryXORCirclePhase (1 : ZMod 2) = (-1 : Circle) := by
  apply Circle.coe_injective
  have h : ((ZMod.toCircle (1 : ZMod 2) : Circle) : ℂ) = -1 := by
    change ((ZMod.toCircle ((1 : ℕ) : ZMod 2) : Circle) : ℂ) = -1
    rw [ZMod.toCircle_natCast]
    ring_nf
    rw [Complex.exp_pi_mul_I]
  exact h

theorem binaryXORCirclePhase_zero_ne_one :
    binaryXORCirclePhase (0 : ZMod 2) ≠ binaryXORCirclePhase (1 : ZMod 2) := by
  intro h
  have hc : ((1 : Circle) : ℂ) = ((-1 : Circle) : ℂ) := by
    simpa [binaryXORCirclePhase_zero, binaryXORCirclePhase_one] using
      congrArg (fun z : Circle => (z : ℂ)) h
  norm_num at hc

/-- A MERP phase assignment: one unit phase per player and question. -/
abbrev MERPPhaseAssignment (Question : Type uQ) :=
  Fin 4 → Question → Circle

/-- A phase assignment satisfies a game when every positive-weight signed
clause has the target phase product. -/
def SatisfiesMERPPhaseAssignment
    (G : FiniteFourPlayerXORGame Question) (phase : MERPPhaseAssignment Question) :
    Prop :=
  ∀ signedClause : SignedFourPlayerClause Question,
    signedClause ∈ G.support →
      (∏ p : Fin 4, phase p (signedClause.1 p)) =
        binaryXORCirclePhase signedClause.2

/-- A game has a perfect MERP strategy when a satisfying phase assignment
exists. -/
def HasPerfectMERPStrategy (G : FiniteFourPlayerXORGame Question) : Prop :=
  ∃ phase : MERPPhaseAssignment Question,
    SatisfiesMERPPhaseAssignment G phase

/-- The four-qubit computational basis. -/
abbrev FourQubitBasis := Fin 4 → Fin 2

theorem fin_two_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by
  fin_cases i <;> simp

/-- Flip the chosen player's bit and leave the others fixed. -/
def qubitFlip (p : Fin 4) (x : FourQubitBasis) : FourQubitBasis :=
  Function.update x p (if x p = 0 then (1 : Fin 2) else 0)

theorem qubitFlip_apply_self (p : Fin 4) (x : FourQubitBasis) :
    qubitFlip p x p ≠ x p := by
  rcases fin_two_eq_zero_or_one (x p) with h0 | h1
  · simp [qubitFlip, h0]
  · simp [qubitFlip, h1]

theorem qubitFlip_apply_ne (p : Fin 4) (x : FourQubitBasis) {i : Fin 4}
    (hi : i ≠ p) :
    qubitFlip p x i = x i := by
  simp [qubitFlip, hi]

theorem qubitFlip_involutive (p : Fin 4) (x : FourQubitBasis) :
    qubitFlip p (qubitFlip p x) = x := by
  funext i
  by_cases hi : i = p
  · subst i
    rcases fin_two_eq_zero_or_one (x p) with h0 | h1
    · simp [qubitFlip, h0]
    · simp [qubitFlip, h1]
  · simp [qubitFlip, hi]

theorem qubitFlip_ne_self (p : Fin 4) (x : FourQubitBasis) :
    qubitFlip p x ≠ x := by
  intro h
  exact qubitFlip_apply_self p x (congrFun h p)

theorem qubitFlip_commute {p q : Fin 4} (hpq : p ≠ q) (x : FourQubitBasis) :
    qubitFlip p (qubitFlip q x) = qubitFlip q (qubitFlip p x) := by
  funext i
  by_cases hi : i = p
  · subst i
    rcases fin_two_eq_zero_or_one (x q) with hq0 | hq1
    · simp [qubitFlip, hpq, hq0]
    · simp [qubitFlip, hpq, hq1]
  · by_cases hiq : i = q
    · subst i
      rcases fin_two_eq_zero_or_one (x p) with hp0 | hp1
      · simp [qubitFlip, hpq, hi, hp0]
      · simp [qubitFlip, hpq, hi, hp1]
    · simp [qubitFlip, hi, hiq]

/-- The local equatorial observable: flips the player's bit and multiplies by
`u` or `conj u` according to the input bit. -/
def merpLocalObservable (u : Circle) (p : Fin 4) : CMatrix FourQubitBasis :=
  fun x y =>
    if y = qubitFlip p x then
      if y p = 0 then (u : ℂ) else star (u : ℂ)
    else 0

/-- The local equatorial observable is Hermitian. -/
theorem merpLocalObservable_isHermitian (u : Circle) (p : Fin 4) :
    (merpLocalObservable u p).IsHermitian := by
  ext x y
  simp [merpLocalObservable, Matrix.conjTranspose_apply]
  by_cases hxy : y = qubitFlip p x
  · rw [if_pos hxy]
    rcases fin_two_eq_zero_or_one (x p) with hx0 | hx1
    · have hy : y p = 1 := by
        rw [hxy]
        simp [qubitFlip, hx0]
      have hxy' : x = qubitFlip p y := by
        calc
          x = qubitFlip p (qubitFlip p x) := (qubitFlip_involutive p x).symm
          _ = qubitFlip p y := by rw [hxy]
      rw [hxy']
      simp [qubitFlip, hy]
    · have hy : y p = 0 := by
        rw [hxy]
        simp [qubitFlip, hx1]
      have hxy' : x = qubitFlip p y := by
        calc
          x = qubitFlip p (qubitFlip p x) := (qubitFlip_involutive p x).symm
          _ = qubitFlip p y := by rw [hxy]
      rw [hxy']
      simp [qubitFlip, hy]
  · rw [if_neg hxy]
    have hx : x ≠ qubitFlip p y := by
      intro hx
      apply hxy
      calc
        y = qubitFlip p (qubitFlip p y) := (qubitFlip_involutive p y).symm
        _ = qubitFlip p x := by rw [hx]
    simp [hx]

/-- The product `u * star u` is one for unit complex phases. -/
theorem circle_mul_star_self (u : Circle) :
    (u : ℂ) * star (u : ℂ) = 1 := by
  rw [Complex.star_def]
  rw [← Circle.coe_inv_eq_conj]
  exact mul_inv_cancel₀ (Circle.coe_ne_zero u)

/-- The local equatorial observable is an involution. -/
theorem merpLocalObservable_involutive (u : Circle) (p : Fin 4) :
    merpLocalObservable u p * merpLocalObservable u p = 1 := by
  ext x y
  by_cases hxy : x = y
  · subst y
    rw [Matrix.mul_apply]
    have hsingle :
        (∑ z : FourQubitBasis,
            merpLocalObservable u p x z * merpLocalObservable u p z x) =
          merpLocalObservable u p x (qubitFlip p x) *
            merpLocalObservable u p (qubitFlip p x) x := by
      refine Finset.sum_eq_single (qubitFlip p x) ?_ ?_
      · intro z hz hne
        by_cases hz1 : z = qubitFlip p x
        · exact False.elim (hne hz1)
        · simp [merpLocalObservable, hz1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hsingle]
    rcases fin_two_eq_zero_or_one (x p) with hx0 | hx1
    · have hflip : (qubitFlip p x) p = 1 := by
        simp [qubitFlip, hx0]
      simp [merpLocalObservable, qubitFlip_involutive, hx0, hflip,
        mul_comm]
      exact circle_mul_star_self u
    · have hflip : (qubitFlip p x) p = 0 := by
        simp [qubitFlip, hx1]
      simp [merpLocalObservable, qubitFlip_involutive, hx1, hflip,
        mul_comm]
      exact circle_mul_star_self u
  · rw [Matrix.mul_apply]
    simp [hxy]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hz1 : z = qubitFlip p x
    · have hz2 : z ≠ qubitFlip p y := by
        intro hzy
        apply hxy
        calc
          x = qubitFlip p (qubitFlip p x) := (qubitFlip_involutive p x).symm
          _ = qubitFlip p z := by rw [hz1]
          _ = qubitFlip p (qubitFlip p y) := by rw [hzy]
          _ = y := qubitFlip_involutive p y
      have hyx : y ≠ qubitFlip p (qubitFlip p x) := by
        intro hy
        apply hxy
        rw [hy, qubitFlip_involutive]
      simp [merpLocalObservable, hz1, hyx]
    · simp [merpLocalObservable, hz1]

/-- Pointwise evaluation of a product of two local equatorial observables on
distinct players, left factor first. -/
private theorem merp_mul_apply_flip_left (u : Circle) (p : Fin 4)
    (v : Circle) (q : Fin 4) (hpq : p ≠ q) (x y : FourQubitBasis) :
    (merpLocalObservable u p * merpLocalObservable v q) x y =
      if y = qubitFlip q (qubitFlip p x) then
        (if (qubitFlip p x) p = 0 then (u : ℂ) else star (u : ℂ)) *
          (if y q = 0 then (v : ℂ) else star (v : ℂ))
      else 0 := by
  rw [Matrix.mul_apply]
  by_cases hy : y = qubitFlip q (qubitFlip p x)
  · rw [if_pos hy]
    have hsingle :
        (∑ z : FourQubitBasis,
            merpLocalObservable u p x z * merpLocalObservable v q z y) =
          merpLocalObservable u p x (qubitFlip p x) *
            merpLocalObservable v q (qubitFlip p x) y := by
      refine Finset.sum_eq_single (qubitFlip p x) ?_ ?_
      · intro z hz hne
        by_cases hz1 : z = qubitFlip p x
        · exact False.elim (hne hz1)
        · simp [merpLocalObservable, hz1]
      · intro hnot
        exact False.elim (hnot (Finset.mem_univ _))
    rw [hsingle]
    rw [hy]
    simp [merpLocalObservable]
  · rw [if_neg hy]
    apply Finset.sum_eq_zero
    intro z hz
    by_cases hz1 : z = qubitFlip p x
    · have hz3 : ¬ y = qubitFlip q z := by
        intro hyz
        apply hy
        rw [hz1] at hyz
        exact hyz
      simp [merpLocalObservable, hz1, hz3]
      intro hyx
      exact False.elim (hy hyx)
    · simp [merpLocalObservable, hz1]

/-- The local equatorial observables of distinct players commute. -/
theorem merpLocalObservable_cross_commute {p q : Fin 4} (hpq : p ≠ q)
    (u v : Circle) :
    Commute (merpLocalObservable u p) (merpLocalObservable v q) := by
  ext x y
  rw [merp_mul_apply_flip_left u p v q hpq x y]
  rw [merp_mul_apply_flip_left v q u p hpq.symm x y]
  have hflip : qubitFlip q (qubitFlip p x) = qubitFlip p (qubitFlip q x) :=
    (qubitFlip_commute hpq x).symm
  rw [hflip]
  by_cases hy : y = qubitFlip p (qubitFlip q x)
  · rw [if_pos hy, if_pos hy]
    have hyq : y q = (qubitFlip q x) q := by
      rw [hy]
      simp [qubitFlip, hpq, hpq.symm]
    have hyp : y p = (qubitFlip p x) p := by
      rw [hy]
      simp [qubitFlip, hpq, hpq.symm]
    rw [hyq, hyp]
    rw [mul_comm]
  · rw [if_neg hy, if_neg hy]

/-- A target conflict excludes every perfect MERP strategy. -/
theorem conflictingTargets_exclude_perfectMERPStrategy
    (G : FiniteFourPlayerXORGame Question) :
    G.HasConflictingTargets → ¬ HasPerfectMERPStrategy G := by
  rintro hconflict ⟨phase, hperfect⟩
  rcases hconflict with ⟨query, h0, h1⟩
  have hp0 := hperfect (query, (0 : ZMod 2))
    ((G.mem_support_iff (query, (0 : ZMod 2))).mpr h0)
  have hp1 := hperfect (query, (1 : ZMod 2))
    ((G.mem_support_iff (query, (1 : ZMod 2))).mpr h1)
  exact binaryXORCirclePhase_zero_ne_one (hp0.symm.trans hp1)

/-- The four-qubit GHZ amplitude supported on the all-zero and all-one basis
vectors. -/
def ghzAmp : FourQubitBasis → ℂ :=
  fun x =>
    if (∀ i : Fin 4, x i = 0) ∨ (∀ i : Fin 4, x i = 1)
      then ((1 / Real.sqrt 2 : ℝ) : ℂ)
      else 0

theorem ghzAmp_all_zero :
    ghzAmp (fun _ : Fin 4 => (0 : Fin 2)) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [ghzAmp]

theorem ghzAmp_all_one :
    ghzAmp (fun _ : Fin 4 => (1 : Fin 2)) = ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
  simp [ghzAmp]

/-- The normalized GHZ pure vector. -/
noncomputable def ghzPure : PureVector FourQubitBasis :=
  { amp := ghzAmp
    trace_rankOne_eq_one := by
      classical
      have hcoeff :
          ((1 / Real.sqrt 2 : ℝ) : ℂ) * star (((1 / Real.sqrt 2 : ℝ) : ℂ)) =
            ((1 / 2 : ℝ) : ℂ) := by
        have hstar : star (((1 / Real.sqrt 2 : ℝ) : ℂ)) =
            ((1 / Real.sqrt 2 : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hstar]
        have hsqrt : (Real.sqrt 2 : ℝ) ≠ 0 := by positivity
        field_simp [hsqrt]
        have hdiv : (((1 / Real.sqrt 2 : ℝ) : ℂ) ^ 2) = ((1 / 2 : ℝ) : ℂ) := by
          norm_num [← Complex.ofReal_pow, Real.sq_sqrt]
        exact hdiv
      rw [rankOneMatrix_trace]
      change (∑ x : FourQubitBasis, ghzAmp x * star (ghzAmp x)) = 1
      let zero : FourQubitBasis := fun _ : Fin 4 => (0 : Fin 2)
      let one : FourQubitBasis := fun _ : Fin 4 => (1 : Fin 2)
      have hf (x : FourQubitBasis) :
          ghzAmp x * star (ghzAmp x) = 0 ∨ x = zero ∨ x = one := by
        by_cases h0 : ∀ i : Fin 4, x i = 0
        · right; left; exact funext h0
        · by_cases h1 : ∀ i : Fin 4, x i = 1
          · right; right; exact funext h1
          · left
            simp [ghzAmp, h0, h1]
      have hzero_mem : zero ∈ (Finset.univ : Finset FourQubitBasis) :=
        Finset.mem_univ _
      have hone_mem : one ∈ (Finset.univ : Finset FourQubitBasis) :=
        Finset.mem_univ _
      have hzero_ne_one : zero ≠ one := by
        intro h
        have h01 : (0 : Fin 2) ≠ 1 := by decide
        exact h01 (by simpa [zero, one] using congrFun h 0)
      have htail :
          (∑ x ∈ (Finset.univ : Finset FourQubitBasis).erase zero,
              ghzAmp x * star (ghzAmp x)) =
            ghzAmp one * star (ghzAmp one) := by
        refine Finset.sum_eq_single one ?_ ?_
        · intro b hb hne
          have hb_ne_zero : b ≠ zero := by
            intro hb0
            exact (Finset.mem_erase.mp hb).1 hb0
          rcases hf b with hzero | hbzero | hbone
          · exact hzero
          · exact False.elim (hb_ne_zero hbzero)
          · subst b
            exact False.elim (hne rfl)
        · intro hnot
          exact False.elim (hnot (by
            exact Finset.mem_erase.mpr ⟨hzero_ne_one.symm, hone_mem⟩))
      have htotal :=
        Finset.sum_erase_add
          (s := (Finset.univ : Finset FourQubitBasis))
          (f := fun x : FourQubitBasis => ghzAmp x * star (ghzAmp x))
          (a := zero) hzero_mem
      rw [htail, add_comm] at htotal
      have hzero_val : ghzAmp zero * star (ghzAmp zero) = ((1 / 2 : ℝ) : ℂ) := by
        simpa [ghzAmp_all_zero, zero] using hcoeff
      have hone_val : ghzAmp one * star (ghzAmp one) = ((1 / 2 : ℝ) : ℂ) := by
        simpa [ghzAmp_all_one, one] using hcoeff
      rw [htotal.symm]
      change (ghzAmp zero * star (ghzAmp zero)) +
          (ghzAmp one * star (ghzAmp one)) = 1
      rw [hzero_val, hone_val]
      norm_num }

/-- The explicit four-qubit MERP observable strategy. -/
noncomputable def merpObservableStrategy
    (phase : MERPPhaseAssignment Question) :
    FourPlayerBinaryObservableStrategy Question FourQubitBasis where
  state := ghzPure
  observable := fun p q => merpLocalObservable (phase p q) p
  isHermitian := fun p q => merpLocalObservable_isHermitian (phase p q) p
  involutive := fun p q => merpLocalObservable_involutive (phase p q) p
  cross_commute := fun {p p'} hne q q' =>
    merpLocalObservable_cross_commute hne (phase p q) (phase p' q')

/-- The ordered product of local equatorial matrices over a player list. -/
noncomputable def merpListMatrix
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question)
    : List (Fin 4) → CMatrix FourQubitBasis
  | [] => 1
  | p :: ps =>
      merpLocalObservable (phase p (query p)) p * merpListMatrix phase query ps

/-- The basis vector obtained by flipping the bits of the listed players. -/
def merpListFold : List (Fin 4) → FourQubitBasis → FourQubitBasis
  | [], x => x
  | p :: ps, x => qubitFlip p (merpListFold ps x)

/-- The accumulated complex phase along the listed flips, read from the input
state. -/
noncomputable def merpListPhase
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question) :
    List (Fin 4) → FourQubitBasis → ℂ
  | [], _ => 1
  | p :: ps, x =>
      merpListPhase phase query ps x *
        (if (merpListFold ps x) p = 0 then (phase p (query p) : ℂ)
          else star (phase p (query p) : ℂ))

/-- A list product acting on a delta basis vector is a single flipped
delta vector with the accumulated phase. -/
private theorem merpListMatrix_mulVec_delta_apply
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question)
    (players : List (Fin 4)) (x y : FourQubitBasis) :
    Matrix.mulVec (merpListMatrix phase query players)
        (fun z : FourQubitBasis => if z = y then (1 : ℂ) else 0) x =
      if x = merpListFold players y then merpListPhase phase query players y else 0 := by
  induction players generalizing x y with
  | nil =>
      simp [merpListMatrix, merpListFold, merpListPhase, Matrix.one_mulVec]
  | cons p ps ih =>
      simp only [merpListMatrix]
      rw [← Matrix.mulVec_mulVec
        (fun z : FourQubitBasis => if z = y then (1 : ℂ) else 0)
        (merpLocalObservable (phase p (query p)) p) (merpListMatrix phase query ps)]
      have hinner :
          Matrix.mulVec (merpListMatrix phase query ps)
              (fun z : FourQubitBasis => if z = y then (1 : ℂ) else 0) =
            fun z : FourQubitBasis =>
              if z = merpListFold ps y then merpListPhase phase query ps y else 0 := by
        funext z
        exact ih z y
      rw [hinner]
      simp [Matrix.mulVec, merpLocalObservable]
      change (∑ i : FourQubitBasis,
          (if i = qubitFlip p x then
              (if i p = 0 then ↑(phase p (query p)) else star ↑(phase p (query p))) else 0) *
            (if i = merpListFold ps y then merpListPhase phase query ps y else 0)) =
        if x = merpListFold (p :: ps) y then merpListPhase phase query (p :: ps) y else 0
      by_cases hz : merpListFold ps y = qubitFlip p x
      · rw [hz]
        simp
        have hxfold : x = merpListFold (p :: ps) y := by
          rw [merpListFold]
          exact ((by
            rw [hz, qubitFlip_involutive]) : qubitFlip p (merpListFold ps y) = x).symm
        rw [if_pos hxfold]
        have hphase_def : merpListPhase phase query (p :: ps) y =
            merpListPhase phase query ps y *
              (if (merpListFold ps y) p = 0 then ↑(phase p (query p))
                else star ↑(phase p (query p))) := rfl
        rw [hphase_def]
        rw [hz]
        by_cases hcond : (qubitFlip p x) p = 0
        · simp [hcond]
          rw [mul_comm]
        · simp [hcond]
          rw [mul_comm]
      · have hsum_zero :
            (∑ i : FourQubitBasis,
              (if i = qubitFlip p x then
                  (if i p = 0 then ↑(phase p (query p)) else star ↑(phase p (query p))) else 0) *
                (if i = merpListFold ps y then merpListPhase phase query ps y else 0)) = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          by_cases hi1 : i = qubitFlip p x
          · have hi2 : i ≠ merpListFold ps y := by
              intro h
              apply hz
              rw [← h, hi1]
            simp [hi1, hi2]
            intro h
            exact False.elim (hz h.symm)
          · simp [hi1]
        rw [hsum_zero]
        have hxnot : ¬ x = merpListFold (p :: ps) y := by
          intro hx
          apply hz
          rw [merpListFold] at hx
          calc
            merpListFold ps y = qubitFlip p (qubitFlip p (merpListFold ps y)) :=
              (qubitFlip_involutive p (merpListFold ps y)).symm
            _ = qubitFlip p x := by rw [hx]
        simp [hxnot]

/-- The four-qubit flip used by the MERP clause operator. -/
def merpFlipAll (x : FourQubitBasis) : FourQubitBasis :=
  merpListFold fourPlayerOrder x

/-- The clause matrix of the MERP strategy is the ordered product of the four
local equatorial matrices. -/
noncomputable def merpClauseMatrix
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question) :
    CMatrix FourQubitBasis :=
  clauseObservable (ClauseId := PUnit.{1}) (merpObservableStrategy phase)
    (fun _ : PUnit.{1} => query) PUnit.unit

theorem merpClauseMatrix_eq_listMatrix
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question) :
    merpClauseMatrix phase query = merpListMatrix phase query fourPlayerOrder := by
  unfold merpClauseMatrix
  rw [clauseObservable_eq_four_product]
  simp [merpObservableStrategy, merpListMatrix, fourPlayerOrder, mul_assoc]

/-- Flipping all four qubits maps the all-zero basis vector to all-one. -/
theorem merpFlipAll_zero :
    merpFlipAll (fun _ : Fin 4 => (0 : Fin 2)) = fun _ : Fin 4 => (1 : Fin 2) := by
  funext i
  fin_cases i <;> simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip]

/-- Flipping all four qubits maps the all-one basis vector to all-zero. -/
theorem merpFlipAll_one :
    merpFlipAll (fun _ : Fin 4 => (1 : Fin 2)) = fun _ : Fin 4 => (0 : Fin 2) := by
  funext i
  fin_cases i <;> simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip]

/-- Flipping all four qubits is an involution. -/
theorem merpFlipAll_involutive (x : FourQubitBasis) :
    merpFlipAll (merpFlipAll x) = x := by
  funext i
  fin_cases i
  · rcases fin_two_eq_zero_or_one (x 0) with h0 | h1
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h0]
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h1]
  · rcases fin_two_eq_zero_or_one (x 1) with h0 | h1
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h0]
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h1]
  · rcases fin_two_eq_zero_or_one (x 2) with h0 | h1
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h0]
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h1]
  · rcases fin_two_eq_zero_or_one (x 3) with h0 | h1
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h0]
    · simp [merpFlipAll, merpListFold, fourPlayerOrder, qubitFlip, h1]

/-- The accumulated phase from the all-zero basis vector is the product of
the four phases. -/
theorem merpListPhase_fourPlayerOrder_zero (phase : MERPPhaseAssignment Question)
    (query : FourPlayerQuestionTuple Question) :
    merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => (0 : Fin 2)) =
      (∏ p : Fin 4, (phase p (query p) : ℂ)) := by
  simp [merpListPhase, merpListFold, fourPlayerOrder, Fin.prod_univ_succ, qubitFlip]
  ring

/-- The accumulated phase from the all-one basis vector is the product of the
conjugated phases. -/
theorem merpListPhase_fourPlayerOrder_one (phase : MERPPhaseAssignment Question)
    (query : FourPlayerQuestionTuple Question) :
    merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => (1 : Fin 2)) =
      (∏ p : Fin 4, star (phase p (query p) : ℂ)) := by
  simp [merpListPhase, merpListFold, fourPlayerOrder, Fin.prod_univ_succ, qubitFlip]
  ring

private theorem ghzAmp_eq (x : FourQubitBasis) :
    ghzAmp x =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) *
          (if x = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) +
        ((1 / Real.sqrt 2 : ℝ) : ℂ) *
          (if x = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) := by
  by_cases h0 : x = (fun _ : Fin 4 => (0 : Fin 2))
  · subst x
    have h01 : (fun _ : Fin 4 => (0 : Fin 2)) ≠ (fun _ : Fin 4 => (1 : Fin 2)) := by
      decide
    simp [ghzAmp, h01]
  · by_cases h1 : x = (fun _ : Fin 4 => (1 : Fin 2))
    · subst x
      have h10 : (fun _ : Fin 4 => (1 : Fin 2)) ≠ (fun _ : Fin 4 => (0 : Fin 2)) := by
        decide
      simp [ghzAmp, h10]
    · have hnot0 : ¬ (∀ i : Fin 4, x i = 0) := by
        intro h
        exact h0 (funext h)
      have hnot1 : ¬ (∀ i : Fin 4, x i = 1) := by
        intro h
        exact h1 (funext h)
      simp [ghzAmp, hnot0, hnot1, h0, h1]

private theorem merp_phase_star_product (phase : MERPPhaseAssignment Question)
    (query : FourPlayerQuestionTuple Question) (b : ZMod 2)
    (hphase : (∏ p : Fin 4, phase p (query p)) = binaryXORCirclePhase b) :
    (∏ p : Fin 4, star (phase p (query p) : ℂ)) = binaryXORPhase b := by
  have hprod : (∏ p : Fin 4, (phase p (query p) : ℂ)) = binaryXORPhase b := by
    apply congrArg (fun z : Circle => (z : ℂ)) hphase
  have hmap : (∏ p : Fin 4, star ((phase p (query p) : ℂ))) =
      star (∏ p : Fin 4, (phase p (query p) : ℂ)) := by
    simpa using (map_prod (starRingEnd ℂ) (fun p : Fin 4 => (phase p (query p) : ℂ))
      (Finset.univ : Finset (Fin 4)))
  rw [hmap, hprod]
  by_cases hb : b = 0
  · simp [hb]
  · have hb1 : b = 1 := by
      rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb0 | hb1
      · exact False.elim (hb hb0)
      · exact hb1
    simp [hb1, binaryXORPhase_one]

private theorem merpClauseMatrix_mulVec_ghz_zero
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question) :
    Matrix.mulVec (merpClauseMatrix phase query) ghzAmp (fun _ : Fin 4 => (0 : Fin 2)) =
      ((1 / Real.sqrt 2 : ℝ) : ℂ) *
        (∏ p : Fin 4, star (phase p (query p) : ℂ)) := by
  let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  let x : FourQubitBasis := fun _ : Fin 4 => (0 : Fin 2)
  have hdelta (y : FourQubitBasis) :
      Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
          (fun z : FourQubitBasis => if z = y then (1 : ℂ) else 0) x =
        if x = merpListFold fourPlayerOrder y
          then merpListPhase phase query fourPlayerOrder y else 0 :=
    merpListMatrix_mulVec_delta_apply phase query fourPlayerOrder x y
  rw [merpClauseMatrix_eq_listMatrix]
  have hlin :
      Matrix.mulVec (merpListMatrix phase query fourPlayerOrder) ghzAmp x =
        c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
              (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) x +
          c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
              (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) x := by
    rw [show ghzAmp = fun z : FourQubitBasis =>
        c * (if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) +
          c * (if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) by
      funext z
      simpa [c] using ghzAmp_eq z]
    change Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
        (c • (fun z : FourQubitBasis =>
          if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) +
         c • (fun z : FourQubitBasis =>
          if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0)) x =
      c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
            (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) x +
        c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
            (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) x
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp
  rw [hlin]
  rw [hdelta (fun _ : Fin 4 => (0 : Fin 2)),
    hdelta (fun _ : Fin 4 => (1 : Fin 2))]
  change ((c * if x = merpFlipAll (fun _ : Fin 4 => (0 : Fin 2))
        then merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => 0) else 0) +
      c * if x = merpFlipAll (fun _ : Fin 4 => (1 : Fin 2))
        then merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => 1) else 0) =
    c * (∏ p : Fin 4, star (phase p (query p) : ℂ))
  rw [merpFlipAll_zero, merpFlipAll_one,
    merpListPhase_fourPlayerOrder_zero, merpListPhase_fourPlayerOrder_one]
  have h01 : (fun _ : Fin 4 => (0 : Fin 2)) ≠
      (fun _ : Fin 4 => (1 : Fin 2)) := by decide
  simp [x, h01]

private theorem circlePhase_eq_of_coe (z : Circle) (b : ZMod 2)
    (h : (z : ℂ) = binaryXORPhase b) :
    z = binaryXORCirclePhase b := by
  apply Circle.coe_injective
  rw [binaryXORCirclePhase]
  rw [← ZMod.stdAddChar_apply]
  exact h

/-- The MERP clause matrix acts on the GHZ state by the target binary phase
whenever the phase-product solvability condition holds. -/
theorem merp_clauseOperator_mul_ghz (phase : MERPPhaseAssignment Question)
    (query : FourPlayerQuestionTuple Question) (b : ZMod 2)
    (hphase : (∏ p : Fin 4, phase p (query p)) = binaryXORCirclePhase b) :
    Matrix.mulVec (merpClauseMatrix phase query) ghzAmp =
      binaryXORPhase b • ghzAmp := by
  funext x
  let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
  have hdelta (y : FourQubitBasis) :
      Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
          (fun z : FourQubitBasis => if z = y then (1 : ℂ) else 0) x =
        if x = merpListFold fourPlayerOrder y
          then merpListPhase phase query fourPlayerOrder y else 0 :=
    merpListMatrix_mulVec_delta_apply phase query fourPlayerOrder x y
  rw [merpClauseMatrix_eq_listMatrix]
  have hlin :
      Matrix.mulVec (merpListMatrix phase query fourPlayerOrder) ghzAmp x =
        c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
              (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) x +
          c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
              (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) x := by
    rw [show ghzAmp = fun z : FourQubitBasis =>
        c * (if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) +
          c * (if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) by
      funext z
      simpa [c] using ghzAmp_eq z]
    change Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
        (c • (fun z : FourQubitBasis =>
          if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) +
         c • (fun z : FourQubitBasis =>
          if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0)) x =
      c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
            (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (0 : Fin 2)) then 1 else 0) x +
        c * Matrix.mulVec (merpListMatrix phase query fourPlayerOrder)
            (fun z : FourQubitBasis => if z = (fun _ : Fin 4 => (1 : Fin 2)) then 1 else 0) x
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    simp
  rw [hlin]
  rw [hdelta (fun _ : Fin 4 => (0 : Fin 2)),
    hdelta (fun _ : Fin 4 => (1 : Fin 2))]
  change ((c * if x = merpFlipAll (fun _ : Fin 4 => (0 : Fin 2))
        then merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => 0) else 0) +
      c * if x = merpFlipAll (fun _ : Fin 4 => (1 : Fin 2))
        then merpListPhase phase query fourPlayerOrder (fun _ : Fin 4 => 1) else 0) =
    (binaryXORPhase b • ghzAmp) x
  rw [merpFlipAll_zero, merpFlipAll_one,
    merpListPhase_fourPlayerOrder_zero, merpListPhase_fourPlayerOrder_one]
  have hprod : (∏ p : Fin 4, (phase p (query p) : ℂ)) = binaryXORPhase b := by
    apply congrArg (fun z : Circle => (z : ℂ)) hphase
  have hstar := merp_phase_star_product phase query b hphase
  by_cases hx0 : x = (fun _ : Fin 4 => (0 : Fin 2))
  · subst x
    have h01 : (fun _ : Fin 4 => (0 : Fin 2)) ≠
        (fun _ : Fin 4 => (1 : Fin 2)) := by decide
    rw [if_neg h01]
    rw [hstar]
    simp [c, ghzAmp_all_zero]
    rw [mul_comm]
  · by_cases hx1 : x = (fun _ : Fin 4 => (1 : Fin 2))
    · subst x
      have h10 : (fun _ : Fin 4 => (1 : Fin 2)) ≠
          (fun _ : Fin 4 => (0 : Fin 2)) := by decide
      rw [if_neg h10]
      rw [hprod]
      simp [c, ghzAmp_all_one]
      rw [mul_comm]
    · have hnot0 : ¬ (∀ i : Fin 4, x i = 0) := by
        intro h
        exact hx0 (funext h)
      have hnot1 : ¬ (∀ i : Fin 4, x i = 1) := by
        intro h
        exact hx1 (funext h)
      simp [c, hprod, hstar, hx0, hx1, hnot0, hnot1, ghzAmp]

/-- The MERP strategy satisfies a signed clause exactly when the phase product
matches the target sign. -/
theorem merpObservableStrategy_satisfies_clause_iff_phase_product
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question)
    (b : ZMod 2) :
    IsPerfectFourPlayerBinaryObservableStrategy
        (fun _ : PUnit.{1} => query) (fun _ : PUnit.{1} => b)
        (merpObservableStrategy phase) ↔
      (∏ p : Fin 4, phase p (query p)) = binaryXORCirclePhase b := by
  constructor
  · intro hperfect
    have haction := hperfect PUnit.unit
    have hzero := merpClauseMatrix_mulVec_ghz_zero phase query
    let c : ℂ := ((1 / Real.sqrt 2 : ℝ) : ℂ)
    have hzero_eq :
        c * (∏ p : Fin 4, star (phase p (query p) : ℂ)) =
          binaryXORPhase b * c := by
      have haction' : Matrix.mulVec (merpClauseMatrix phase query) ghzAmp
          (fun _ : Fin 4 => (0 : Fin 2)) =
          binaryXORPhase b * ghzAmp (fun _ : Fin 4 => (0 : Fin 2)) := by
        simpa [merpClauseMatrix, merpObservableStrategy] using
          congrFun haction (fun _ : Fin 4 => (0 : Fin 2))
      rw [hzero] at haction'
      simpa [c, ghzAmp_all_zero] using haction'
    have hc_ne : c ≠ 0 := by
      dsimp [c]
      norm_num [Real.sq_sqrt]
    have hstar : (∏ p : Fin 4, star (phase p (query p) : ℂ)) = binaryXORPhase b := by
      apply mul_left_cancel₀ hc_ne
      calc
        c * (∏ p : Fin 4, star (phase p (query p) : ℂ)) = binaryXORPhase b * c := hzero_eq
        _ = c * binaryXORPhase b := by rw [mul_comm]
    have hprod : (∏ p : Fin 4, (phase p (query p) : ℂ)) = binaryXORPhase b := by
      have hmap : (∏ p : Fin 4, (phase p (query p) : ℂ)) =
          star (∏ p : Fin 4, star (phase p (query p) : ℂ)) := by
        simpa [star_star] using
          (map_prod (starRingEnd ℂ) (fun p : Fin 4 => star (phase p (query p) : ℂ))
            (Finset.univ : Finset (Fin 4))).symm
      rw [hmap, hstar]
      by_cases hb : b = 0
      · simp [hb]
      · have hb1 : b = 1 := by
          rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb0 | hb1
          · exact False.elim (hb hb0)
          · exact hb1
        simp [hb1, binaryXORPhase_one]
    exact circlePhase_eq_of_coe (∏ p : Fin 4, phase p (query p)) b
      (by simpa using hprod)
  · intro hphase
    intro unit
    change Matrix.mulVec (merpClauseMatrix phase query) ghzAmp =
      binaryXORPhase b • ghzAmp
    exact merp_clauseOperator_mul_ghz phase query b hphase

/-- A satisfying MERP phase assignment gives an exact perfect observable
strategy on the reduced support. -/
theorem satisfyingMERPPhaseAssignment_gives_perfectObservableStrategy
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (phase : MERPPhaseAssignment Question)
    (hphase : SatisfiesMERPPhaseAssignment G phase) :
    IsPerfectFourPlayerBinaryObservableStrategy G.reducedQuery
        (G.reducedSign hconflict) (merpObservableStrategy phase) := by
  intro c
  simpa [IsPerfectFourPlayerBinaryObservableStrategy] using
    (merpObservableStrategy_satisfies_clause_iff_phase_product phase c.1
      (G.reducedSign hconflict c)).mpr
      (hphase (c.1, G.reducedSign hconflict c)
        (G.reducedSignedClause_mem_support hconflict c))

abbrev QubitHilbert := EuclideanSpace ℂ FourQubitBasis

noncomputable def matrixToContinuous (M : CMatrix FourQubitBasis) :
    QubitHilbert →L[ℂ] QubitHilbert :=
  LinearMap.toContinuousLinearMap M.toEuclideanLin

private theorem matrixToContinuous_mul (M N : CMatrix FourQubitBasis) :
    matrixToContinuous M * matrixToContinuous N = matrixToContinuous (M * N) := by
  ext x i
  simp [matrixToContinuous, Matrix.toLpLin_mul]

private theorem matrixToContinuous_one :
    matrixToContinuous (1 : CMatrix FourQubitBasis) = 1 := by
  ext x i
  simp [matrixToContinuous, Matrix.toLpLin_one]

theorem matrixToContinuous_isSelfAdjoint (M : CMatrix FourQubitBasis)
    (hM : M.IsHermitian) :
    IsSelfAdjoint (matrixToContinuous M) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  change M.toEuclideanLin.IsSymmetric
  exact (Matrix.isSymmetric_toEuclideanLin_iff).mpr hM

noncomputable def ghzContinuousState : QubitHilbert :=
  WithLp.toLp 2 ghzAmp

theorem ghzContinuousState_norm : ‖ghzContinuousState‖ = 1 := by
  have hinner : (inner ℂ ghzContinuousState ghzContinuousState) = 1 := by
    rw [PiLp.inner_apply]
    change (∑ i : FourQubitBasis, inner ℂ (ghzAmp i) (ghzAmp i)) = 1
    rw [show (∑ i : FourQubitBasis, inner ℂ (ghzAmp i) (ghzAmp i)) =
        ∑ i : FourQubitBasis, ghzAmp i * star (ghzAmp i) by
      apply Finset.sum_congr rfl
      intro i hi
      simp [inner, mul_comm]]
    simpa [rankOneMatrix_trace, rankOneMatrix_apply, Matrix.trace] using
      ghzPure.trace_rankOne_eq_one
  have hsq : ‖ghzContinuousState‖ ^ 2 = 1 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) ghzContinuousState]
    rw [hinner]
    norm_num
  nlinarith [norm_nonneg ghzContinuousState]

noncomputable def merpContinuousStrategy (phase : MERPPhaseAssignment Question) :
    FourPlayerCommutingOperatorStrategy Question QubitHilbert where
  state := ghzContinuousState
  state_norm := ghzContinuousState_norm
  observable := fun p q => matrixToContinuous (merpLocalObservable (phase p q) p)
  isSelfAdjoint := fun p q =>
    matrixToContinuous_isSelfAdjoint (merpLocalObservable (phase p q) p)
      (merpLocalObservable_isHermitian (phase p q) p)
  involutive := fun p q => by
    rw [matrixToContinuous_mul, merpLocalObservable_involutive, matrixToContinuous_one]
  cross_commute := fun {p p'} hne q q' => by
    unfold Commute
    change matrixToContinuous (merpLocalObservable (phase p q) p) *
        matrixToContinuous (merpLocalObservable (phase p' q') p') =
      matrixToContinuous (merpLocalObservable (phase p' q') p') *
        matrixToContinuous (merpLocalObservable (phase p q) p)
    rw [matrixToContinuous_mul, matrixToContinuous_mul]
    congr 1
    exact merpLocalObservable_cross_commute hne (phase p q) (phase p' q')

private theorem merpContinuousStrategy_clauseOperator_eq
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question) :
    (merpContinuousStrategy phase).clauseOperator query =
      matrixToContinuous (merpClauseMatrix phase query) := by
  simp [FourPlayerCommutingOperatorStrategy.clauseOperator, merpContinuousStrategy,
    matrixToContinuous_mul,
    merpClauseMatrix_eq_listMatrix, merpListMatrix, fourPlayerOrder]
  congr 1
  simp [mul_assoc]

private theorem merpContinuousStrategy_satisfies_iff
    (phase : MERPPhaseAssignment Question) (query : FourPlayerQuestionTuple Question)
    (b : ZMod 2) :
    (merpContinuousStrategy phase).SatisfiesSignedClause query b ↔
      Matrix.mulVec (merpClauseMatrix phase query) ghzAmp =
        binaryXORPhase b • ghzAmp := by
  constructor
  · intro h
    change (merpContinuousStrategy phase).clauseOperator query ghzContinuousState =
      binaryXORPhase b • ghzContinuousState at h
    funext i
    have hpoint := congrArg (fun f : QubitHilbert => f i) h
    simpa [FourPlayerCommutingOperatorStrategy.SatisfiesSignedClause,
      merpContinuousStrategy_clauseOperator_eq,
      ghzContinuousState, matrixToContinuous, Matrix.toLpLin_apply, Pi.smul_apply] using hpoint
  · intro h
    change (merpContinuousStrategy phase).clauseOperator query ghzContinuousState =
      binaryXORPhase b • ghzContinuousState
    apply PiLp.ext
    intro i
    simpa [FourPlayerCommutingOperatorStrategy.SatisfiesSignedClause,
      merpContinuousStrategy_clauseOperator_eq,
      ghzContinuousState, matrixToContinuous, Matrix.toLpLin_apply, Pi.smul_apply] using
      congrFun h i

/-- A perfect MERP strategy yields a perfect commuting-operator strategy. -/
theorem perfectMERP_implies_hasPerfectCommutingOperatorStrategy
    (G : FiniteFourPlayerXORGame Question) :
    HasPerfectMERPStrategy G →
      FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G := by
  rintro ⟨phase, hphase⟩
  by_cases hconflict : G.HasConflictingTargets
  · exact False.elim (conflictingTargets_exclude_perfectMERPStrategy G hconflict ⟨phase, hphase⟩)
  · exact ⟨{
      Hilbert := ULift.{max uQ 0, 0} QubitHilbert
      normedAddCommGroup := inferInstance
      innerProductSpace := inferInstance
      completeSpace := inferInstance
      strategy := FourPlayerCommutingOperatorStrategy.uliftStrategy (merpContinuousStrategy phase)
      perfect := by
        intro clause hclause
        exact (FourPlayerCommutingOperatorStrategy.uliftStrategy_satisfiesSignedClause_iff
          (merpContinuousStrategy phase) clause.1 clause.2).mpr (by
            rw [merpContinuousStrategy_satisfies_iff]
            exact merp_clauseOperator_mul_ghz phase clause.1 clause.2 (hphase clause hclause))
    }⟩

end

end XORGame
end QIT

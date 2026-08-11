/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.GeneralObservableStrategy
public import XORGameFormalization.SemanticCompletion.GameNormalization
public import XORGameFormalization.Value
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Real.Archimedean
public import Mathlib.Tactic

/-!
# Quantitative refutation gap for commuting-operator strategies

This module defines the genuine numerical commuting-operator value of a
weighted XOR game as the supremum of expected winning probabilities over
bundled commuting correlations.  It then derives an explicit positive gap
from any operator refutation.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uH uC uT

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

/-- A bundled commuting correlation on a game: a complete complex inner
product space together with a commuting-operator strategy. -/
structure CommutingCorrelation (G : FiniteFourPlayerXORGame Question) where
  Hilbert : Type (max uQ 0)
  instNorm : NormedAddCommGroup Hilbert
  instInner : InnerProductSpace ℂ Hilbert
  instComplete : CompleteSpace Hilbert
  strategy : FourPlayerCommutingOperatorStrategy Question Hilbert

/-- The winning probability of one signed clause in a commuting strategy. -/
def clauseWinProbability
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) : ℝ :=
  (1 +
      (inner ℂ strategy.state
        (binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state)).re) / 2

/-- The expected winning probability of a strategy under the game weights. -/
def expectedWin
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) : ℝ :=
  ∑ clause : SignedFourPlayerClause Question,
    G.weight clause * clauseWinProbability strategy clause

/-- The set of realized expected winning probabilities. -/
def commutingOperatorValues (G : FiniteFourPlayerXORGame Question) : Set ℝ :=
  {v | ∃ corr : CommutingCorrelation G,
    letI := corr.instNorm
    letI := corr.instInner
    letI := corr.instComplete
    expectedWin G corr.strategy = v}

/-- The numerical commuting-operator value of a game. -/
def commutingOperatorValue (G : FiniteFourPlayerXORGame Question) : ℝ :=
  sSup (commutingOperatorValues G)

private theorem observable_mem_unitary
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (p : Fin 4) (q : Question) :
    strategy.observable p q ∈ unitary (Hilbert →L[ℂ] Hilbert) := by
  apply IsUnit.mem_unitary_of_star_mul_self
  · exact ⟨⟨strategy.observable p q, strategy.observable p q,
      strategy.involutive p q, strategy.involutive p q⟩, rfl⟩
  · rw [strategy.isSelfAdjoint p q, strategy.involutive p q]

private theorem observable_norm_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (p : Fin 4) (q : Question) :
    ‖strategy.observable p q‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one ?_
  intro x
  rw [ContinuousLinearMap.norm_map_of_mem_unitary (observable_mem_unitary strategy p q) x]
  simp

private theorem clauseOperator_norm_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    ‖strategy.clauseOperator query‖ ≤ 1 := by
  rw [FourPlayerCommutingOperatorStrategy.clauseOperator]
  calc
    ‖(strategy.observable 0 (query 0) * strategy.observable 1 (query 1)) *
        strategy.observable 2 (query 2) * strategy.observable 3 (query 3)‖ ≤
      ‖strategy.observable 0 (query 0) * strategy.observable 1 (query 1) *
          strategy.observable 2 (query 2)‖ * ‖strategy.observable 3 (query 3)‖ :=
        norm_mul_le _ _
    _ ≤ (‖strategy.observable 0 (query 0) * strategy.observable 1 (query 1)‖ *
          ‖strategy.observable 2 (query 2)‖) * ‖strategy.observable 3 (query 3)‖ := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ ((‖strategy.observable 0 (query 0)‖ * ‖strategy.observable 1 (query 1)‖) *
          ‖strategy.observable 2 (query 2)‖) * ‖strategy.observable 3 (query 3)‖ := by
          gcongr
          exact norm_mul_le _ _
    _ ≤ 1 := by
          have h0 : 0 ≤ ‖strategy.observable 0 (query 0)‖ := norm_nonneg _
          have h1 : 0 ≤ ‖strategy.observable 1 (query 1)‖ := norm_nonneg _
          have h2 : 0 ≤ ‖strategy.observable 2 (query 2)‖ := norm_nonneg _
          have h3 : 0 ≤ ‖strategy.observable 3 (query 3)‖ := norm_nonneg _
          have h01 : ‖strategy.observable 0 (query 0)‖ * ‖strategy.observable 1 (query 1)‖ ≤ 1 := by
            nlinarith [observable_norm_le_one strategy 0 (query 0),
              observable_norm_le_one strategy 1 (query 1), h0, h1]
          have h012 :
              (‖strategy.observable 0 (query 0)‖ * ‖strategy.observable 1 (query 1)‖) *
                  ‖strategy.observable 2 (query 2)‖ ≤ 1 := by
            nlinarith [h01, observable_norm_le_one strategy 2 (query 2), h0, h1, h2]
          nlinarith [h012, observable_norm_le_one strategy 3 (query 3), h0, h1, h2, h3]

private theorem norm_binaryXORPhase (b : ZMod 2) : ‖binaryXORPhase b‖ = 1 := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
  · simp [hb]
  · simp [hb, binaryXORPhase_one]

private theorem signedClauseOperator_norm_apply_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    ‖binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state‖ ≤ 1 := by
  calc
    ‖binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state‖ =
        ‖binaryXORPhase clause.2‖ * ‖strategy.clauseOperator clause.1 strategy.state‖ := by
          rw [norm_smul]
    _ = ‖strategy.clauseOperator clause.1 strategy.state‖ := by
          rw [norm_binaryXORPhase]
          simp
    _ ≤ ‖strategy.clauseOperator clause.1‖ * ‖strategy.state‖ := by
          exact (strategy.clauseOperator clause.1).le_opNorm strategy.state
    _ ≤ 1 := by
          nlinarith [clauseOperator_norm_le_one strategy clause.1, strategy.state_norm,
            norm_nonneg (strategy.clauseOperator clause.1)]

private theorem signedClauseInner_re_abs_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    |(inner ℂ strategy.state
        (binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state)).re| ≤ 1 := by
  let z : ℂ := inner ℂ strategy.state
      (binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state)
  have hre_sq : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq z]
    simpa [pow_two] using Complex.re_sq_le_normSq z
  have habs := abs_le_of_sq_le_sq hre_sq (norm_nonneg z)
  have hinner := norm_inner_le_norm (𝕜 := ℂ) strategy.state
      (binaryXORPhase clause.2 • strategy.clauseOperator clause.1 strategy.state)
  have hC := signedClauseOperator_norm_apply_le_one strategy clause
  have hle : ‖z‖ ≤ 1 := by
    nlinarith [hinner, hC, strategy.state_norm]
  change |z.re| ≤ 1
  nlinarith [habs, hle]

private theorem clauseOperator_inner_self_re
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    (inner ℂ (strategy.clauseOperator clause.1 strategy.state)
        (strategy.clauseOperator clause.1 strategy.state)).re =
      (inner ℂ strategy.state strategy.state).re := by
  let C := strategy.clauseOperator clause.1
  let ψ := strategy.state
  have hself : IsSelfAdjoint C :=
    FourPlayerCommutingOperatorStrategy.clauseOperator_isSelfAdjoint strategy clause.1
  have hinv : C * C = 1 :=
    FourPlayerCommutingOperatorStrategy.clauseOperator_involutive strategy clause.1
  calc
    (inner ℂ (C ψ) (C ψ)).re = (inner ℂ ψ (C.adjoint (C ψ))).re := by
      rw [← ContinuousLinearMap.adjoint_inner_right C ψ (C ψ)]
    _ = (inner ℂ ψ (C (C ψ))).re := by rw [hself.adjoint_eq]
    _ = (inner ℂ ψ ((C * C) ψ)).re := rfl
    _ = (inner ℂ ψ ψ).re := by rw [hinv]; simp

private theorem clauseOperator_inner_commute_re
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    (inner ℂ (strategy.clauseOperator clause.1 strategy.state) strategy.state).re =
      (inner ℂ strategy.state (strategy.clauseOperator clause.1 strategy.state)).re := by
  let C := strategy.clauseOperator clause.1
  let ψ := strategy.state
  have hself : IsSelfAdjoint C :=
    FourPlayerCommutingOperatorStrategy.clauseOperator_isSelfAdjoint strategy clause.1
  calc
    (inner ℂ (C ψ) ψ).re = (inner ℂ ψ (C.adjoint ψ)).re := by
      rw [← ContinuousLinearMap.adjoint_inner_right C ψ ψ]
    _ = (inner ℂ ψ (C ψ)).re := by rw [hself.adjoint_eq]

private theorem binaryXORPhase_conj (b : ZMod 2) :
    star (binaryXORPhase b) = binaryXORPhase b := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
  · simp [hb]
  · simp [hb, binaryXORPhase_one]

private theorem binaryXORPhase_mul_conj (b : ZMod 2) :
    binaryXORPhase b * star (binaryXORPhase b) = 1 := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
  · simp [hb]
  · simp [hb, binaryXORPhase_one]

private theorem binaryXORPhase_im_eq_zero (b : ZMod 2) :
    (binaryXORPhase b).im = 0 := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
  · simp [hb]
  · simp [hb, binaryXORPhase_one]

private theorem binaryXORPhase_re_sq (b : ZMod 2) :
    (binaryXORPhase b).re ^ 2 = 1 := by
  rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb | hb
  · simp [hb]
  · simp [hb, binaryXORPhase_one]

private theorem binaryXORPhase_re_sq_mul_norm
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    (binaryXORPhase clause.2).re ^ 2 * ((‖strategy.state‖ ^ 2 : ℝ) : ℂ).re = 1 := by
  rw [binaryXORPhase_re_sq clause.2]
  rw [Complex.ofReal_re, strategy.state_norm]
  norm_num

private theorem binaryXORPhase_list_prod
    {ClauseId : Type uC} (sign : ClauseId → ZMod 2) (word : List ClauseId) :
    (word.map (fun c => binaryXORPhase (sign c))).prod =
      binaryXORPhase ((word.map sign).sum) := by
  induction word with
  | nil => simp
  | cons c tail ih =>
      simp [List.map_cons, List.sum_cons, ih, binaryXORPhase_add, mul_comm]

private theorem clauseOperator_norm_apply_eq_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    ‖strategy.clauseOperator clause.1 strategy.state‖ = 1 := by
  let C := strategy.clauseOperator clause.1
  let ψ := strategy.state
  have hCC := clauseOperator_inner_self_re strategy clause
  have hnorm : ‖C ψ‖ ^ 2 = (inner ℂ (C ψ) (C ψ)).re := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (C ψ)
    simpa using h.symm
  have hpsi : (inner ℂ ψ ψ).re = 1 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) ψ
    rw [strategy.state_norm] at h
    simpa [ψ] using h
  have hsq : ‖C ψ‖ ^ 2 = 1 := by
    rw [hnorm, hCC, hpsi]
  have hnonneg : 0 ≤ ‖C ψ‖ := norm_nonneg _
  nlinarith

/-- The clause winning probability is nonnegative. -/
theorem clauseWinProbability_nonneg
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    0 ≤ clauseWinProbability strategy clause := by
  unfold clauseWinProbability
  have hbdd := signedClauseInner_re_abs_le_one strategy clause
  nlinarith [abs_le.mp hbdd]

/-- The clause winning probability is at most one. -/
theorem clauseWinProbability_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    clauseWinProbability strategy clause ≤ 1 := by
  unfold clauseWinProbability
  have hbdd := signedClauseInner_re_abs_le_one strategy clause
  nlinarith [abs_le.mp hbdd]

/-- The squared defect norm is four times the clause winning loss. -/
theorem clauseDefect_norm_sq
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    ‖strategy.clauseOperator clause.1 strategy.state -
        binaryXORPhase clause.2 • strategy.state‖ ^ 2 =
      4 * (1 - clauseWinProbability strategy clause) := by
  let C := strategy.clauseOperator clause.1
  let ψ := strategy.state
  let phase := binaryXORPhase clause.2
  have hnorm : ‖C ψ - phase • ψ‖ ^ 2 =
      (inner ℂ (C ψ - phase • ψ) (C ψ - phase • ψ)).re := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (C ψ - phase • ψ)
    simpa using h.symm
  change ‖C ψ - phase • ψ‖ ^ 2 = 4 * (1 - clauseWinProbability strategy clause)
  rw [hnorm]
  have hCC := clauseOperator_inner_self_re strategy clause
  have hsym := clauseOperator_inner_commute_re strategy clause
  have hphase_conj := binaryXORPhase_conj clause.2
  have hphase_mul := binaryXORPhase_mul_conj clause.2
  have hpsi : (inner ℂ ψ ψ).re = 1 := by
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) ψ
    rw [strategy.state_norm] at h
    simpa [ψ] using h
  have hpsi_norm : ((‖ψ‖ ^ 2 : ℝ) : ℂ).re = 1 := by
    rw [Complex.ofReal_re]
    rw [show ‖ψ‖ ^ 2 = 1 by
      rw [show ‖ψ‖ = 1 by simpa [ψ] using strategy.state_norm]
      norm_num]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right]
  simp [C, ψ, hCC, hsym, hphase_conj, hphase_mul, hpsi, phase, clauseWinProbability,
    hpsi_norm, binaryXORPhase_im_eq_zero, binaryXORPhase_re_sq,
    clauseOperator_norm_apply_eq_one]
  have hinner_smul :
      (inner ℂ ψ (phase • C ψ)).re = phase.re * (inner ℂ ψ (C ψ)).re := by
    simp [inner_smul_right]
    have hconj : star phase = phase := by
      simpa [phase] using binaryXORPhase_conj clause.2
    have hphase_im : phase.im = 0 := by
      simpa [phase] using binaryXORPhase_im_eq_zero clause.2
    simp [hconj, hphase_im]
  rw [hinner_smul]
  simp [phase]
  have hterm := binaryXORPhase_re_sq_mul_norm strategy clause
  ring_nf at hterm ⊢
  rw [strategy.state_norm]
  simp [C, ψ]
  rw [binaryXORPhase_re_sq clause.2]
  ring

/-- A clause wins with probability one exactly when its signed clause
operator fixes the strategy state as an eigenvector. -/
theorem clauseWinProbability_eq_one_iff_satisfies
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    clauseWinProbability strategy clause = 1 ↔
      FourPlayerCommutingOperatorStrategy.SatisfiesSignedClause
        strategy clause.1 clause.2 := by
  have hsq := clauseDefect_norm_sq strategy clause
  constructor
  · intro hp
    have hnorm_sq : ‖strategy.clauseOperator clause.1 strategy.state -
          binaryXORPhase clause.2 • strategy.state‖ ^ 2 = 0 := by
      nlinarith [hsq, hp]
    have hnorm : ‖strategy.clauseOperator clause.1 strategy.state -
          binaryXORPhase clause.2 • strategy.state‖ = 0 := by
      exact sq_eq_zero_iff.mp hnorm_sq
    have hsub : strategy.clauseOperator clause.1 strategy.state -
          binaryXORPhase clause.2 • strategy.state = 0 := by
      exact norm_eq_zero.mp hnorm
    exact sub_eq_zero.mp hsub
  · intro hs
    have hnorm_sq : ‖strategy.clauseOperator clause.1 strategy.state -
          binaryXORPhase clause.2 • strategy.state‖ ^ 2 = 0 := by
      rw [hs]
      simp
    have hp : 4 * (1 - clauseWinProbability strategy clause) = 0 := by
      rw [← hsq]
      exact hnorm_sq
    nlinarith

private theorem clauseDefect_apply
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    ‖(strategy.clauseOperator clause.1 -
        binaryXORPhase clause.2 • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ =
      ‖strategy.clauseOperator clause.1 strategy.state -
        binaryXORPhase clause.2 • strategy.state‖ := by
  rw [ContinuousLinearMap.sub_apply]
  simp

private theorem scalarListProd_apply
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [NormedSpace ℂ Hilbert]
    (zs : List ℂ) (ψ : Hilbert) :
    ((zs.map (fun z => z • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ =
      (zs.prod : ℂ) • ψ := by
  induction zs with
  | nil => simp
  | cons z rest ih =>
      simp [ih, mul_smul]

private theorem list_norm_prod_le_one (l : List ℂ)
    (h : ∀ x ∈ l, ‖x‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  calc
    ‖l.prod‖ ≤ (l.map norm).prod := l.norm_prod_le
    _ ≤ 1 := by
      induction l with
      | nil => simp
      | cons x rest ih =>
          simp only [List.map_cons, List.prod_cons]
          have hrest_nonneg : 0 ≤ (rest.map norm).prod :=
            List.prod_nonneg (by
              intro y hy
              rcases List.mem_map.mp hy with ⟨z, hz, rfl⟩
              exact norm_nonneg z)
          exact mul_le_one₀ (h x (by simp)) hrest_nonneg
            (ih (by intro y hy; exact h y (by simp [hy])))

private theorem list_sum_le_length_mul_maximum (l : List ℝ) (h : l ≠ []) :
    l.sum ≤ l.length * (l.maximum_of_length_pos (List.length_pos_of_ne_nil h)) := by
  induction l with
  | nil => cases h rfl
  | cons x rest ih =>
      have hlen : 0 < (x :: rest).length := List.length_pos_of_ne_nil h
      have hle_cons : ∀ z ∈ (x :: rest), z ≤ (x :: rest).maximum_of_length_pos hlen :=
        fun z hz => List.le_maximum_of_length_pos_of_mem hz hlen
      by_cases hrest_eq : rest = []
      · subst rest
        simp
      · have hlen_rest : 0 < rest.length := List.length_pos_of_ne_nil hrest_eq
        have hx : x ≤ (x :: rest).maximum_of_length_pos hlen :=
          hle_cons x (by simp)
        have hrest_le : rest.maximum_of_length_pos hlen_rest ≤
            (x :: rest).maximum_of_length_pos hlen := by
          exact List.le_maximum_of_length_pos_of_mem
            (by simp [List.maximum_of_length_pos_mem hlen_rest]) hlen
        have hih := ih hrest_eq
        simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
        nlinarith [hx, hrest_le, hih]

private theorem exists_mem_defect_ge
    (defects : List ℝ) (hsum : (2 : ℝ) ≤ defects.sum) (hne : defects ≠ []) :
    ∃ d ∈ defects, (2 : ℝ) / defects.length ≤ d := by
  let m := defects.maximum_of_length_pos (List.length_pos_of_ne_nil hne)
  refine ⟨m, List.maximum_of_length_pos_mem (List.length_pos_of_ne_nil hne), ?_⟩
  have hlen_pos : (0 : ℝ) < defects.length := by
    exact_mod_cast List.length_pos_of_ne_nil hne
  have hle := list_sum_le_length_mul_maximum defects hne
  have hmax : (2 : ℝ) / defects.length ≤ m := by
    rw [div_le_iff₀ hlen_pos]
    nlinarith
  exact hmax

private theorem norm_product_sub_scalarProduct_le_sum_defects
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [NormedSpace ℂ Hilbert]
    (pairs : List ((Hilbert →L[ℂ] Hilbert) × ℂ)) (ψ : Hilbert)
    (hA : ∀ a ∈ pairs.map Prod.fst, ‖a‖ ≤ 1)
    (hB : ∀ z ∈ pairs.map Prod.snd, ‖z‖ ≤ 1) :
    ‖(pairs.map Prod.fst).prod ψ -
        ((pairs.map (fun p => p.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ‖ ≤
      (pairs.map (fun p => ‖(p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ‖)).sum := by
  induction pairs with
  | nil => simp
  | cons p ps ih =>
      simp
      have htail : ‖(ps.map Prod.fst).prod ψ -
          ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ‖ ≤
        (ps.map (fun q => ‖(q.1 - q.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ‖)).sum := by
        exact ih (by intro x hx; exact hA x (by simp [hx]))
                 (by intro x hx; exact hB x (by simp [hx]))
      have htri : ‖p.1 ((ps.map Prod.fst).prod ψ) - p.2 •
          ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ‖ ≤
          ‖p.1 ((ps.map Prod.fst).prod ψ) -
              p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ +
            ‖p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ) -
                p.2 • ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ := by
          calc
            ‖p.1 ((ps.map Prod.fst).prod ψ) - p.2 •
                ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ‖ =
                ‖(p.1 ((ps.map Prod.fst).prod ψ) -
                    p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)) +
                  (p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ) -
                    p.2 • ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ))‖ := by
                  congr
                  abel
            _ ≤ ‖p.1 ((ps.map Prod.fst).prod ψ) -
                    p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ +
                  ‖p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ) -
                      p.2 • ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ :=
                  norm_add_le _ _
      have h1 : ‖p.1 ((ps.map Prod.fst).prod ψ) -
            p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ ≤
          ‖(ps.map Prod.fst).prod ψ -
              ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ‖ := by
        have hle := p.1.le_opNorm ((ps.map Prod.fst).prod ψ -
          ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ)
        have ha : ‖p.1‖ ≤ 1 := hA p.1 (by simp)
        have hmap : p.1 ((ps.map Prod.fst).prod ψ) -
            p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ) =
          p.1 ((ps.map Prod.fst).prod ψ -
            ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)) := by
          simp [map_sub]
        rw [hmap]
        nlinarith [norm_nonneg ((ps.map Prod.fst).prod ψ -
          ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ))]
      have h2 : ‖p.1 ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ) -
            p.2 • ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod ψ)‖ ≤
          ‖p.1 ψ - p.2 • ψ‖ := by
        have hscalar : ((ps.map (fun q => q.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) ψ =
            (ps.map Prod.snd).prod • ψ := by
          simpa [List.map_map] using scalarListProd_apply (ps.map Prod.snd) ψ
        rw [hscalar]
        have hlin : (p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert))
            ((ps.map Prod.snd).prod • ψ) =
            (ps.map Prod.snd).prod •
              ((p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ) := by
          simp [ContinuousLinearMap.sub_apply, smul_sub, smul_smul]
        have hsame : p.1 ((ps.map Prod.snd).prod • ψ) -
              p.2 • ((ps.map Prod.snd).prod • ψ) =
            (p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert))
              ((ps.map Prod.snd).prod • ψ) := by
          simp [ContinuousLinearMap.sub_apply, smul_sub, smul_smul, mul_comm]
        rw [hsame, hlin, norm_smul]
        have hdef : (p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ =
            p.1 ψ - p.2 • ψ := by
          simp [ContinuousLinearMap.sub_apply]
        rw [← hdef]
        have hnorm : ‖(ps.map Prod.snd).prod‖ ≤ 1 := by
          exact list_norm_prod_le_one (ps.map Prod.snd : List ℂ) (by
            intro x hx
            exact hB x (by simp [hx]))
        have hc_x : ‖(ps.map Prod.snd).prod‖ *
              ‖(p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ‖ ≤
            ‖(p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ‖ := by
          simpa using mul_le_mul_of_nonneg_right hnorm
            (norm_nonneg ((p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ))
        nlinarith
      have hdefs : (ps.map (fun q => ‖(q.1 - q.2 • (1 : Hilbert →L[ℂ] Hilbert)) ψ‖)).sum =
          (ps.map (fun q => ‖q.1 ψ - q.2 • ψ‖)).sum := by
        congr 1
      rw [hdefs] at htail
      nlinarith

private theorem refutationWord_defect_sum_lower
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId)
    (href : IsOperatorRefutation query sign word) :
    (2 : ℝ) ≤
      (word.map (fun c => ‖(strategy.clauseOperator (query c) -
          binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖)).sum := by
  let pairs := word.map (fun c => (strategy.clauseOperator (query c), binaryXORPhase (sign c)))
  have htele := norm_product_sub_scalarProduct_le_sum_defects pairs strategy.state
    (by
      intro a ha
      rcases List.mem_map.mp ha with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨c, hc, rfl⟩
      exact clauseOperator_norm_le_one strategy (query c))
    (by
      intro z hz
      rcases List.mem_map.mp hz with ⟨p, hp, rfl⟩
      rcases List.mem_map.mp hp with ⟨c, hc, rfl⟩
      simpa using norm_binaryXORPhase (sign c))
  have hword : (pairs.map Prod.fst).prod =
      FourPlayerCommutingOperatorStrategy.observableProfileEval strategy
        (wordProfile query word) := by
    simpa [pairs] using
      FourPlayerCommutingOperatorStrategy.word_operatorProduct_eq_observableProfileEval
        query strategy word
  have hLHS : ‖(pairs.map Prod.fst).prod strategy.state -
      ((pairs.map (fun p => p.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) strategy.state‖ = 2 := by
    rw [hword]
    have hbal :=
      FourPlayerCommutingOperatorStrategy.balancedWord_operatorProduct_eq_identity
        query strategy word href.1
    rw [hbal]
    have hscalar : ((pairs.map (fun p => p.2 • (1 : Hilbert →L[ℂ] Hilbert))).prod) strategy.state =
        (word.map (fun c => binaryXORPhase (sign c))).prod • strategy.state := by
      simpa [pairs] using scalarListProd_apply
        (word.map (fun c => binaryXORPhase (sign c))) strategy.state
    rw [hscalar]
    have hprod := binaryXORPhase_list_prod sign word
    rw [hprod]
    have hsum : (word.map sign).sum = 1 := by
      rw [← parityPairing_occurrenceParity]
      exact href.2
    rw [hsum]
    simp [binaryXORPhase_one]
    rw [show strategy.state + strategy.state = (2 : ℂ) • strategy.state by
      simp [two_smul]]
    rw [norm_smul]
    norm_num [strategy.state_norm]
  have hRHS : (pairs.map (fun p => ‖(p.1 - p.2 • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖)).sum =
      (word.map (fun c => ‖(strategy.clauseOperator (query c) -
          binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖)).sum := by
    apply congrArg List.sum
    simp only [pairs]
    simp only [List.map_map, Function.comp_apply]
    apply List.map_congr_left
    intro c hc
    have hv : (strategy.clauseOperator (query c) -
          binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state =
        (strategy.clauseOperator (query c)) strategy.state -
          binaryXORPhase (sign c) • strategy.state := by
      rw [ContinuousLinearMap.sub_apply]
      simp
    simpa [Function.comp_apply, hv]
  rw [hLHS] at htele
  simpa [pairs] using htele

/-- The expected winning probability is nonnegative. -/
theorem expectedWin_nonneg
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    0 ≤ expectedWin G strategy := by
  unfold expectedWin
  exact Finset.sum_nonneg (by
    intro clause hclause
    exact mul_nonneg (G.weight_nonneg clause) (clauseWinProbability_nonneg strategy clause))

/-- The expected winning probability is at most one. -/
theorem expectedWin_le_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    expectedWin G strategy ≤ 1 := by
  unfold expectedWin
  have hle : (∑ clause : SignedFourPlayerClause Question,
      G.weight clause * clauseWinProbability strategy clause) ≤
    ∑ clause : SignedFourPlayerClause Question, G.weight clause * 1 := by
    exact Finset.sum_le_sum (by
      intro clause hclause
      exact mul_le_mul_of_nonneg_left (clauseWinProbability_le_one strategy clause)
        (G.weight_nonneg clause))
  calc
    (∑ clause : SignedFourPlayerClause Question,
        G.weight clause * clauseWinProbability strategy clause) ≤
      ∑ clause : SignedFourPlayerClause Question, G.weight clause * 1 := hle
    _ = 1 := by
      simp [G.weight_sum_one]

/-- Lifting preserves signed-clause satisfaction. -/
theorem liftCommutingStrategy_satisfiesSignedClause_iff
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) (sign : ZMod 2) :
    ((FourPlayerCommutingOperatorStrategy.uliftStrategy strategy :
        FourPlayerCommutingOperatorStrategy Question (ULift.{uT, uH} Hilbert)).SatisfiesSignedClause
          query sign) ↔
      strategy.SatisfiesSignedClause query sign :=
  (FourPlayerCommutingOperatorStrategy.uliftStrategy_satisfiesSignedClause_iff
    strategy query sign)

/-- Lifting preserves the clause winning probability. -/
theorem clauseWinProbability_liftCommutingStrategy
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (clause : SignedFourPlayerClause Question) :
    clauseWinProbability
      (FourPlayerCommutingOperatorStrategy.uliftStrategy strategy :
        FourPlayerCommutingOperatorStrategy Question (ULift.{uT, uH} Hilbert)) clause =
      clauseWinProbability strategy clause := by
  unfold clauseWinProbability
  congr 1

/-- Lifting preserves the expected winning probability. -/
theorem expectedWin_liftCommutingStrategy
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    expectedWin G
      (FourPlayerCommutingOperatorStrategy.uliftStrategy strategy :
        FourPlayerCommutingOperatorStrategy Question (ULift.{uT, uH} Hilbert)) =
      expectedWin G strategy := by
  simp [expectedWin, clauseWinProbability_liftCommutingStrategy]

/-- A universe-zero strategy lifted into the fixed game-group universe and
packaged as a commuting correlation. -/
def liftCommutingCorrelation (G : FiniteFourPlayerXORGame Question)
    {Hilbert : Type 0} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    CommutingCorrelation G where
  Hilbert := ULift.{max uQ 0, 0} Hilbert
  instNorm := inferInstance
  instInner := inferInstance
  instComplete := inferInstance
  strategy := FourPlayerCommutingOperatorStrategy.uliftStrategy strategy

/-- The identity-observable strategy on the one-dimensional complex space. -/
private def identityCommutingStrategy (Question : Type uQ) :
    FourPlayerCommutingOperatorStrategy Question ℂ where
  state := (1 : ℂ)
  state_norm := by norm_num
  observable := fun _ _ => 1
  isSelfAdjoint := by
    intro p q
    simp [IsSelfAdjoint]
  involutive := by
    intro p q
    simp
  cross_commute := by
    intro p p' hne q q'
    simp

/-- The set of realized expected winning probabilities is nonempty. -/
theorem commutingOperatorValues_nonempty (G : FiniteFourPlayerXORGame Question) :
    (commutingOperatorValues G).Nonempty := by
  refine ⟨expectedWin G
    (FourPlayerCommutingOperatorStrategy.uliftStrategy (identityCommutingStrategy Question)), ?_⟩
  exact ⟨liftCommutingCorrelation G (identityCommutingStrategy Question), rfl⟩

/-- The set of realized expected winning probabilities is bounded above. -/
theorem commutingOperatorValues_bddAbove (G : FiniteFourPlayerXORGame Question) :
    BddAbove (commutingOperatorValues G) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨corr, rfl⟩
  letI := corr.instNorm
  letI := corr.instInner
  letI := corr.instComplete
  exact expectedWin_le_one G corr.strategy

/-- The commuting-operator value is nonnegative. -/
theorem commutingOperatorValue_nonneg (G : FiniteFourPlayerXORGame Question) :
    0 ≤ commutingOperatorValue G := by
  unfold commutingOperatorValue
  let v := expectedWin G
    (FourPlayerCommutingOperatorStrategy.uliftStrategy (identityCommutingStrategy Question))
  have hmem : v ∈ commutingOperatorValues G := by
    refine ⟨liftCommutingCorrelation G (identityCommutingStrategy Question), rfl⟩
  have hle := le_csSup (commutingOperatorValues_bddAbove G) hmem
  have h0 : 0 ≤ v := by
    dsimp [v]
    rw [expectedWin_liftCommutingStrategy G (identityCommutingStrategy Question)]
    exact expectedWin_nonneg G (identityCommutingStrategy Question)
  linarith

/-- The commuting-operator value is at most one. -/
theorem commutingOperatorValue_le_one (G : FiniteFourPlayerXORGame Question) :
    commutingOperatorValue G ≤ 1 := by
  unfold commutingOperatorValue
  apply csSup_le (commutingOperatorValues_nonempty G)
  rintro _ ⟨corr, rfl⟩
  letI := corr.instNorm
  letI := corr.instInner
  letI := corr.instComplete
  exact expectedWin_le_one G corr.strategy

namespace FiniteFourPlayerXORGame

variable (G : FiniteFourPlayerXORGame Question)

/-- The minimum positive weight on the support. -/
noncomputable def minimumPositiveWeight (G : FiniteFourPlayerXORGame Question) : ℝ :=
  G.support.inf' G.support_nonempty (fun clause => G.weight clause)

/-- The minimum positive weight is positive. -/
theorem minimumPositiveWeight_pos (G : FiniteFourPlayerXORGame Question) :
    0 < G.minimumPositiveWeight := by
  classical
  unfold minimumPositiveWeight
  rw [Finset.lt_inf'_iff G.support_nonempty]
  intro clause hclause
  exact (G.mem_support_iff clause).mp hclause

/-- The minimum positive weight bounds every supported weight from below. -/
theorem minimumPositiveWeight_le (G : FiniteFourPlayerXORGame Question)
    {clause : SignedFourPlayerClause Question} (hclause : clause ∈ G.support) :
    G.minimumPositiveWeight ≤ G.weight clause := by
  classical
  unfold minimumPositiveWeight
  exact Finset.inf'_le (fun clause => G.weight clause) hclause

end FiniteFourPlayerXORGame

variable {ClauseId : Type uC}

/-- One clause in a refutation word carries a weighted loss at least
`minimumPositiveWeight / word.length ^ 2`. -/
theorem exists_clause_weightedLoss_ge
    [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId)
    (href : IsOperatorRefutation query sign word)
    (hsupport : ∀ c ∈ word, (query c, sign c) ∈ G.support) :
    ∃ c ∈ word,
      G.minimumPositiveWeight / (word.length : ℝ) ^ 2 ≤
        G.weight (query c, sign c) *
          (1 - clauseWinProbability strategy (query c, sign c)) := by
  classical
  let defects := word.map (fun c => ‖(strategy.clauseOperator (query c) -
      binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖)
  have hsum : (2 : ℝ) ≤ defects.sum := by
    simpa [defects] using refutationWord_defect_sum_lower query sign strategy word href
  have hne : defects ≠ [] := by
    intro hdef
    rw [hdef] at hsum
    norm_num at hsum
  rcases exists_mem_defect_ge defects hsum hne with ⟨d, hd, hge⟩
  rcases List.mem_map.mp hd with ⟨c, hc, hd_eq⟩
  subst d
  refine ⟨c, hc, ?_⟩
  have hL : defects.length = word.length := by simp [defects]
  have hword_ne : word ≠ [] := by
    intro hw
    apply hne
    simp [defects, hw]
  have hLpos : (0 : ℝ) < (word.length : ℝ) := by
    exact_mod_cast List.length_pos_of_ne_nil hword_ne
  have hge' : (2 : ℝ) / (word.length : ℝ) ≤
      ‖(strategy.clauseOperator (query c) -
        binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ := by
    simpa [hL] using hge
  have hd_nonneg : 0 ≤ ‖(strategy.clauseOperator (query c) -
      binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ :=
    norm_nonneg _
  have hlo_nonneg : 0 ≤ (2 : ℝ) / (word.length : ℝ) := by positivity
  have hsq_ineq : ((2 : ℝ) / (word.length : ℝ)) ^ 2 ≤
      ‖(strategy.clauseOperator (query c) -
        binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ ^ 2 := by
    simpa [pow_two] using mul_le_mul hge' hge' hlo_nonneg hd_nonneg
  have hsq_id : ‖(strategy.clauseOperator (query c) -
        binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ ^ 2 =
      4 * (1 - clauseWinProbability strategy (query c, sign c)) := by
    rw [clauseDefect_apply strategy (query c, sign c)]
    exact clauseDefect_norm_sq strategy (query c, sign c)
  have hloss4 : (4 : ℝ) / (word.length : ℝ) ^ 2 ≤
      4 * (1 - clauseWinProbability strategy (query c, sign c)) := by
    have hsq_ring : ((2 : ℝ) / (word.length : ℝ)) ^ 2 = 4 / (word.length : ℝ) ^ 2 := by
      field_simp [hLpos.ne']
      ring
    have hsq_ineq' : 4 / (word.length : ℝ) ^ 2 ≤
        ‖(strategy.clauseOperator (query c) -
          binaryXORPhase (sign c) • (1 : Hilbert →L[ℂ] Hilbert)) strategy.state‖ ^ 2 := by
      rwa [← hsq_ring]
    nlinarith [hsq_ineq', hsq_id]
  have hloss : (1 : ℝ) / (word.length : ℝ) ^ 2 ≤
      1 - clauseWinProbability strategy (query c, sign c) := by
    have hloss' : 4 * ((1 : ℝ) / (word.length : ℝ) ^ 2) ≤
        4 * (1 - clauseWinProbability strategy (query c, sign c)) := by
      simpa [one_div, div_eq_mul_inv] using hloss4
    exact (mul_le_mul_iff_right₀ (by norm_num : (0 : ℝ) < 4)).mp hloss'
  have hmin_le : G.minimumPositiveWeight ≤ G.weight (query c, sign c) :=
    G.minimumPositiveWeight_le (hsupport c hc)
  have hw_nonneg : 0 ≤ G.weight (query c, sign c) := G.weight_nonneg _
  have hscale : G.weight (query c, sign c) * ((1 : ℝ) / (word.length : ℝ) ^ 2) ≤
      G.weight (query c, sign c) *
        (1 - clauseWinProbability strategy (query c, sign c)) :=
    mul_le_mul_of_nonneg_left hloss hw_nonneg
  calc
    G.minimumPositiveWeight / (word.length : ℝ) ^ 2 =
        G.minimumPositiveWeight * ((1 : ℝ) / (word.length : ℝ) ^ 2) := by
          rw [div_eq_mul_inv]
          simp [one_div]
    _ ≤ G.weight (query c, sign c) * ((1 : ℝ) / (word.length : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right hmin_le (by positivity)
    _ ≤ G.weight (query c, sign c) *
          (1 - clauseWinProbability strategy (query c, sign c)) := hscale

/-- Every strategy has expected winning probability at most
`1 - minimumPositiveWeight / word.length ^ 2` when a refutation word exists. -/
theorem expectedWin_le_one_sub_refutationGap
    [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId)
    (href : IsOperatorRefutation query sign word)
    (hsupport : ∀ c ∈ word, (query c, sign c) ∈ G.support) :
    expectedWin G strategy ≤
      1 - G.minimumPositiveWeight / (word.length : ℝ) ^ 2 := by
  classical
  rcases exists_clause_weightedLoss_ge G query sign strategy word href hsupport with
    ⟨c, hc, hge⟩
  have hsum : (1 : ℝ) - ∑ clause : SignedFourPlayerClause Question,
      G.weight clause * clauseWinProbability strategy clause =
      ∑ clause : SignedFourPlayerClause Question,
        G.weight clause * (1 - clauseWinProbability strategy clause) := by
    calc
      (1 : ℝ) - ∑ clause : SignedFourPlayerClause Question,
          G.weight clause * clauseWinProbability strategy clause =
          (∑ clause : SignedFourPlayerClause Question, G.weight clause) -
            ∑ clause : SignedFourPlayerClause Question,
              G.weight clause * clauseWinProbability strategy clause := by
            rw [G.weight_sum_one]
      _ = ∑ clause : SignedFourPlayerClause Question,
          (G.weight clause - G.weight clause * clauseWinProbability strategy clause) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ clause : SignedFourPlayerClause Question,
          G.weight clause * (1 - clauseWinProbability strategy clause) := by
            apply Finset.sum_congr rfl
            intro clause hclause
            ring
  have hterm : G.weight (query c, sign c) *
        (1 - clauseWinProbability strategy (query c, sign c)) ≤
      ∑ clause : SignedFourPlayerClause Question,
        G.weight clause * (1 - clauseWinProbability strategy clause) := by
    exact Finset.single_le_sum
      (fun clause hclause => mul_nonneg (G.weight_nonneg clause)
        (sub_nonneg.mpr (clauseWinProbability_le_one strategy clause))) (by simp)
  have hle : G.minimumPositiveWeight / (word.length : ℝ) ^ 2 ≤
      1 - expectedWin G strategy := by
    unfold expectedWin
    rw [hsum]
    exact le_trans hge hterm
  linarith

/-- An operator refutation forces the commuting-operator value strictly below
one, with an explicit positive gap. -/
theorem hasOperatorRefutation_implies_commutingOperatorValue_lt_one
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (href : HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict)) :
    commutingOperatorValue G < 1 := by
  rcases href with ⟨word, hword⟩
  have hsupport : ∀ c ∈ word,
      (G.reducedQuery c, G.reducedSign hconflict c) ∈ G.support := by
    intro c hc
    simpa [FiniteFourPlayerXORGame.reducedSignedClause,
      FiniteFourPlayerXORGame.reducedQuery]
      using G.reducedSignedClause_mem_support hconflict c
  have hword_ne : word ≠ [] := by
    intro hw
    subst word
    have hsum := hword.2
    rw [parityPairing_occurrenceParity] at hsum
    norm_num at hsum
  have hLpos : (0 : ℝ) < (word.length : ℝ) := by
    exact_mod_cast List.length_pos_of_ne_nil hword_ne
  have hgap_pos : 0 < G.minimumPositiveWeight / (word.length : ℝ) ^ 2 := by
    exact div_pos G.minimumPositiveWeight_pos (sq_pos_of_ne_zero (ne_of_gt hLpos))
  have hle : commutingOperatorValue G ≤
      1 - G.minimumPositiveWeight / (word.length : ℝ) ^ 2 := by
    unfold commutingOperatorValue
    apply csSup_le (commutingOperatorValues_nonempty G)
    rintro _ ⟨corr, rfl⟩
    letI := corr.instNorm
    letI := corr.instInner
    letI := corr.instComplete
    exact expectedWin_le_one_sub_refutationGap G G.reducedQuery
      (G.reducedSign hconflict) corr.strategy word hword hsupport
  linarith

/-- A commuting-operator value of one excludes every operator refutation. -/
theorem commutingOperatorValue_eq_one_implies_noOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    commutingOperatorValue G = 1 →
      ¬ HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  intro hval href
  have hlt := hasOperatorRefutation_implies_commutingOperatorValue_lt_one G hconflict href
  linarith

end

end XORGame
end QIT

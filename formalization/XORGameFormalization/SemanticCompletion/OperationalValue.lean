/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.RefutationGap
public import XORGameFormalization.SemanticCompletion.GameGroupDuality
public import XORGameFormalization.SemanticCompletion.MERPStrategy
public import Mathlib.Tactic

/-!
# Operational commuting value and support invariance

This module re-exports the commuting-operator value
(`CommutingCorrelation`, `commutingOperatorValues`, `commutingOperatorValue`)
and derives the value-one duality: a game has commuting-operator value one
exactly when it admits a perfect commuting-operator strategy, which is
exactly when it has no operator refutation.  It also proves that changing
the positive weights without changing the signed support preserves both the
value-one property and the existence of a perfect MERP strategy, and it
records the strict-gap form used by the paper.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uH

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

/-- A strategy that is perfect on the support wins every supported clause and
therefore has expected winning probability one. -/
theorem perfectStrategy_expectedWin_eq_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (hperfect : FourPlayerCommutingOperatorStrategy.IsPerfectCommutingOperatorStrategyOnSupport
      G strategy) :
    expectedWin G strategy = 1 := by
  unfold expectedWin
  calc
    (∑ clause : SignedFourPlayerClause Question,
        G.weight clause * clauseWinProbability strategy clause)
        = ∑ clause : SignedFourPlayerClause Question, G.weight clause := by
          apply Finset.sum_congr rfl
          intro clause hclause
          by_cases hpos : 0 < G.weight clause
          · have hsat : FourPlayerCommutingOperatorStrategy.SatisfiesSignedClause
                strategy clause.1 clause.2 := hperfect clause ((G.mem_support_iff clause).mpr hpos)
            have hprob : clauseWinProbability strategy clause = 1 :=
              (clauseWinProbability_eq_one_iff_satisfies strategy clause).mpr hsat
            rw [hprob, mul_one]
          · have hzero : G.weight clause = 0 :=
              le_antisymm (not_lt.mp hpos) (G.weight_nonneg clause)
            rw [hzero, zero_mul]
    _ = 1 := by
          rw [G.weight_sum_one]

/-- A perfect commuting-operator strategy realizes the value one. -/
theorem hasPerfectCommutingOperatorStrategy_implies_value_eq_one
    (G : FiniteFourPlayerXORGame Question) :
    FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G →
      commutingOperatorValue G = 1 := by
  intro hmodel
  rcases hmodel with ⟨model⟩
  letI := model.normedAddCommGroup
  letI := model.innerProductSpace
  letI := model.completeSpace
  have hone : (1 : ℝ) ∈ commutingOperatorValues G := by
    refine ⟨⟨model.Hilbert, model.normedAddCommGroup, model.innerProductSpace,
      model.completeSpace, model.strategy⟩, ?_⟩
    exact perfectStrategy_expectedWin_eq_one G model.strategy model.perfect
  apply le_antisymm
  · exact commutingOperatorValue_le_one G
  · exact le_csSup (commutingOperatorValues_bddAbove G) hone

/-- The winning probabilities of a clause and its opposite target sum to one. -/
theorem clauseWinProbability_add_opposite_eq_one
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    clauseWinProbability strategy (query, (0 : ZMod 2)) +
      clauseWinProbability strategy (query, (1 : ZMod 2)) = 1 := by
  unfold clauseWinProbability
  simp [binaryXORPhase_zero, binaryXORPhase_one]
  ring

/-- A target conflict forces a strictly positive weighted loss, bounded below
by the minimum of the two conflicting clause weights. -/
private theorem expectedWin_le_one_sub_minWeight_of_conflict
    {Hilbert : Type uH} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question)
    (h0 : 0 < G.weight (query, (0 : ZMod 2)))
    (h1 : 0 < G.weight (query, (1 : ZMod 2))) :
    expectedWin G strategy ≤
      1 - min (G.weight (query, (0 : ZMod 2))) (G.weight (query, (1 : ZMod 2))) := by
  classical
  let m : ℝ := min (G.weight (query, (0 : ZMod 2))) (G.weight (query, (1 : ZMod 2)))
  let p := clauseWinProbability strategy
  have hm_pos : 0 < m := lt_min h0 h1
  have hm_le0 : m ≤ G.weight (query, (0 : ZMod 2)) := min_le_left _ _
  have hm_le1 : m ≤ G.weight (query, (1 : ZMod 2)) := min_le_right _ _
  have hloss0 : 0 ≤ 1 - p (query, (0 : ZMod 2)) :=
    sub_nonneg.mpr (clauseWinProbability_le_one strategy _)
  have hloss1 : 0 ≤ 1 - p (query, (1 : ZMod 2)) :=
    sub_nonneg.mpr (clauseWinProbability_le_one strategy _)
  have hsum01 : 1 - p (query, (0 : ZMod 2)) + (1 - p (query, (1 : ZMod 2))) = 1 := by
    have h := clauseWinProbability_add_opposite_eq_one strategy query
    linarith
  have hterm : m ≤
      G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) +
        G.weight (query, (1 : ZMod 2)) * (1 - p (query, (1 : ZMod 2))) := by
    have hle0 : m * (1 - p (query, (0 : ZMod 2))) ≤
        G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) :=
      mul_le_mul_of_nonneg_right hm_le0 hloss0
    have hle1 : m * (1 - p (query, (1 : ZMod 2))) ≤
        G.weight (query, (1 : ZMod 2)) * (1 - p (query, (1 : ZMod 2))) :=
      mul_le_mul_of_nonneg_right hm_le1 hloss1
    nlinarith [hsum01]
  have hs : (∑ clause : SignedFourPlayerClause Question,
        G.weight clause * (1 - p clause)) =
      G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) +
        G.weight (query, (1 : ZMod 2)) * (1 - p (query, (1 : ZMod 2))) +
          ∑ clause ∈ (Finset.univ.erase (query, (0 : ZMod 2))).erase (query, (1 : ZMod 2)),
            G.weight clause * (1 - p clause) := by
    have hne : (query, (1 : ZMod 2)) ≠ (query, (0 : ZMod 2)) := by simp
    calc
      (∑ clause : SignedFourPlayerClause Question,
          G.weight clause * (1 - p clause))
          = (∑ clause ∈ Finset.univ.erase (query, (0 : ZMod 2)),
              G.weight clause * (1 - p clause)) +
              G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) := by
              rw [← Finset.sum_erase_add (Finset.univ : Finset (SignedFourPlayerClause Question))
                (fun clause : SignedFourPlayerClause Question =>
                  G.weight clause * (1 - p clause))
                (a := (query, (0 : ZMod 2))) (Finset.mem_univ _)]
      _ = (G.weight (query, (1 : ZMod 2)) * (1 - p (query, (1 : ZMod 2))) +
            ∑ clause ∈ (Finset.univ.erase (query, (0 : ZMod 2))).erase (query, (1 : ZMod 2)),
              G.weight clause * (1 - p clause)) +
            G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) := by
            congr 1
            rw [← Finset.sum_erase_add (Finset.univ.erase (query, (0 : ZMod 2)))
              (fun clause : SignedFourPlayerClause Question =>
                G.weight clause * (1 - p clause))
              (a := (query, (1 : ZMod 2))) (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)]
            ring
      _ = G.weight (query, (0 : ZMod 2)) * (1 - p (query, (0 : ZMod 2))) +
            G.weight (query, (1 : ZMod 2)) * (1 - p (query, (1 : ZMod 2))) +
              ∑ clause ∈ (Finset.univ.erase (query, (0 : ZMod 2))).erase (query, (1 : ZMod 2)),
                G.weight clause * (1 - p clause) := by
            ring
  have htotal : m ≤ ∑ clause : SignedFourPlayerClause Question,
      G.weight clause * (1 - p clause) := by
    rw [hs]
    have hrest : 0 ≤ ∑ clause ∈ (Finset.univ.erase (query, (0 : ZMod 2))).erase (query, (1 : ZMod 2)),
        G.weight clause * (1 - p clause) := by
      exact Finset.sum_nonneg (by
        intro clause hclause
        exact mul_nonneg (G.weight_nonneg clause)
          (sub_nonneg.mpr (clauseWinProbability_le_one strategy clause)))
    nlinarith [hterm, hrest]
  have hloss_sum : (1 : ℝ) - expectedWin G strategy =
      ∑ clause : SignedFourPlayerClause Question,
        G.weight clause * (1 - p clause) := by
    calc
      (1 : ℝ) - expectedWin G strategy =
          (∑ clause : SignedFourPlayerClause Question, G.weight clause) -
            ∑ clause : SignedFourPlayerClause Question,
              G.weight clause * p clause := by
            rw [expectedWin, G.weight_sum_one]
      _ = ∑ clause : SignedFourPlayerClause Question,
          (G.weight clause - G.weight clause * p clause) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ clause : SignedFourPlayerClause Question,
          G.weight clause * (1 - p clause) := by
            apply Finset.sum_congr rfl
            intro clause hclause
            ring
  linarith

/-- A target conflict forces the commuting-operator value strictly below one. -/
theorem hasConflictingTargets_implies_commutingOperatorValue_lt_one
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : G.HasConflictingTargets) :
    commutingOperatorValue G < 1 := by
  rcases hconflict with ⟨query, h0, h1⟩
  have hgap_pos : 0 < min (G.weight (query, (0 : ZMod 2))) (G.weight (query, (1 : ZMod 2))) :=
    lt_min h0 h1
  have hle : commutingOperatorValue G ≤
      1 - min (G.weight (query, (0 : ZMod 2))) (G.weight (query, (1 : ZMod 2))) := by
    unfold commutingOperatorValue
    apply csSup_le (commutingOperatorValues_nonempty G)
    rintro _ ⟨corr, rfl⟩
    letI := corr.instNorm
    letI := corr.instInner
    letI := corr.instComplete
    exact expectedWin_le_one_sub_minWeight_of_conflict G corr.strategy query h0 h1
  linarith

/-- The commuting-operator value is one exactly when no operator refutation
exists. -/
theorem commutingOperatorValue_eq_one_iff_noOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    commutingOperatorValue G = 1 ↔
      ¬ HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  constructor
  · exact commutingOperatorValue_eq_one_implies_noOperatorRefutation G hconflict
  · intro hnoref
    exact hasPerfectCommutingOperatorStrategy_implies_value_eq_one G
      (FiniteFourPlayerXORGame.noOperatorRefutation_implies_hasPerfectCommutingOperatorStrategy
        G hconflict hnoref)

/-- The commuting-operator value is one exactly when a perfect commuting
strategy exists. -/
theorem commutingOperatorValue_eq_one_iff_hasPerfectCommutingOperatorStrategy
    (G : FiniteFourPlayerXORGame Question) :
    commutingOperatorValue G = 1 ↔
      FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G := by
  constructor
  · intro hval
    by_cases hconflict : G.HasConflictingTargets
    · have hlt := hasConflictingTargets_implies_commutingOperatorValue_lt_one G hconflict
      linarith
    · exact (FiniteFourPlayerXORGame.hasPerfectCommutingOperatorStrategy_iff_noOperatorRefutation
        G hconflict).mpr
        ((commutingOperatorValue_eq_one_iff_noOperatorRefutation G hconflict).mp hval)
  · intro hperfect
    exact hasPerfectCommutingOperatorStrategy_implies_value_eq_one G hperfect

/-- The reduced clause identifiers of two games with the same signed support
are equivalent by the identity on question tuples. -/
private def reducedClauseEquivOfSupportEq (G H : FiniteFourPlayerXORGame Question)
    (hsupport : G.support = H.support) : G.ReducedClauseId ≃ H.ReducedClauseId where
  toFun c := ⟨c.1, by
    rcases c.2 with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hmemG : (c.1, b) ∈ G.support := (G.mem_support_iff (c.1, b)).mpr hb
    have hmemH : (c.1, b) ∈ H.support := by rwa [← hsupport]
    exact (H.mem_support_iff (c.1, b)).mp hmemH⟩
  invFun c := ⟨c.1, by
    rcases c.2 with ⟨b, hb⟩
    refine ⟨b, ?_⟩
    have hmemH : (c.1, b) ∈ H.support := (H.mem_support_iff (c.1, b)).mpr hb
    have hmemG : (c.1, b) ∈ G.support := by rwa [hsupport]
    exact (G.mem_support_iff (c.1, b)).mp hmemG⟩
  left_inv c := by
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    rfl

/-- Reduced query tuples agree under the support equality. -/
private theorem reducedQuery_of_support_eq (G H : FiniteFourPlayerXORGame Question)
    (hsupport : G.support = H.support) (c : G.ReducedClauseId) :
    H.reducedQuery (reducedClauseEquivOfSupportEq G H hsupport c) = G.reducedQuery c := by
  rfl

/-- Reduced target signs agree under the support equality. -/
private theorem reducedSign_of_support_eq (G H : FiniteFourPlayerXORGame Question)
    (hconflictG : ¬ G.HasConflictingTargets)
    (hconflictH : ¬ H.HasConflictingTargets)
    (hsupport : G.support = H.support) (c : G.ReducedClauseId) :
    H.reducedSign hconflictH (reducedClauseEquivOfSupportEq G H hsupport c) =
      G.reducedSign hconflictG c := by
  have hpos : 0 < H.weight
      ((reducedClauseEquivOfSupportEq G H hsupport c).1, G.reducedSign hconflictG c) := by
    have hmemG : (c.1, G.reducedSign hconflictG c) ∈ G.support :=
      (G.mem_support_iff (c.1, G.reducedSign hconflictG c)).mpr
        (G.reducedSign_supported hconflictG c)
    have hmemH : (c.1, G.reducedSign hconflictG c) ∈ H.support := by
      rwa [← hsupport]
    exact (H.mem_support_iff (c.1, G.reducedSign hconflictG c)).mp hmemH
  exact (H.reducedSign_unique hconflictH
    (reducedClauseEquivOfSupportEq G H hsupport c) (G.reducedSign hconflictG c) hpos).symm

/-- Operator refutations are transported along an equality of signed
supports. -/
private theorem isOperatorRefutation_map_equiv_of_support_eq
    (G H : FiniteFourPlayerXORGame Question)
    (hconflictG : ¬ G.HasConflictingTargets)
    (hconflictH : ¬ H.HasConflictingTargets)
    (hsupport : G.support = H.support) (w : List G.ReducedClauseId) :
    IsOperatorRefutation H.reducedQuery (H.reducedSign hconflictH)
        (w.map (reducedClauseEquivOfSupportEq G H hsupport)) ↔
      IsOperatorRefutation G.reducedQuery (G.reducedSign hconflictG) w := by
  unfold IsOperatorRefutation
  constructor
  · rintro ⟨hb, hp⟩
    constructor
    · intro player
      have hb' := hb player
      have hmap : (w.map (reducedClauseEquivOfSupportEq G H hsupport)).map
            (fun c : H.ReducedClauseId => H.reducedQuery c player) =
          w.map (fun c : G.ReducedClauseId => G.reducedQuery c player) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro c hc
        exact congrFun (reducedQuery_of_support_eq G H hsupport c) player
      rwa [hmap] at hb'
    · have hwsum : (w.map (H.reducedSign hconflictH ∘
          (reducedClauseEquivOfSupportEq G H hsupport))).sum = 1 := by
        simpa [parityPairing_occurrenceParity] using hp
      have hcong : w.map (H.reducedSign hconflictH ∘
            (reducedClauseEquivOfSupportEq G H hsupport)) =
          w.map (G.reducedSign hconflictG) := by
        apply List.map_congr_left
        intro c hc
        exact reducedSign_of_support_eq G H hconflictG hconflictH hsupport c
      rw [parityPairing_occurrenceParity]
      rwa [← hcong]
  · rintro ⟨hb, hp⟩
    constructor
    · intro player
      have hb' := hb player
      have hmap : (w.map (reducedClauseEquivOfSupportEq G H hsupport)).map
            (fun c : H.ReducedClauseId => H.reducedQuery c player) =
          w.map (fun c : G.ReducedClauseId => G.reducedQuery c player) := by
        rw [List.map_map]
        apply List.map_congr_left
        intro c hc
        exact congrFun (reducedQuery_of_support_eq G H hsupport c) player
      rwa [hmap]
    · have hwsum : (w.map (G.reducedSign hconflictG)).sum = 1 := by
        simpa [parityPairing_occurrenceParity] using hp
      have hcong : w.map (H.reducedSign hconflictH ∘
            (reducedClauseEquivOfSupportEq G H hsupport)) =
          w.map (G.reducedSign hconflictG) := by
        apply List.map_congr_left
        intro c hc
        exact reducedSign_of_support_eq G H hconflictG hconflictH hsupport c
      rw [parityPairing_occurrenceParity, List.map_map]
      rwa [hcong]

/-- The existence of an operator refutation depends only on the signed
support, not on the weights. -/
private theorem hasOperatorRefutation_iff_of_support_eq
    (G H : FiniteFourPlayerXORGame Question)
    (hconflictG : ¬ G.HasConflictingTargets)
    (hconflictH : ¬ H.HasConflictingTargets)
    (hsupport : G.support = H.support) :
    HasOperatorRefutation G.reducedQuery (G.reducedSign hconflictG) ↔
      HasOperatorRefutation H.reducedQuery (H.reducedSign hconflictH) := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w.map (reducedClauseEquivOfSupportEq G H hsupport), ?_⟩
    exact (isOperatorRefutation_map_equiv_of_support_eq G H hconflictG hconflictH hsupport w).mpr hw
  · rintro ⟨w, hw⟩
    refine ⟨w.map (reducedClauseEquivOfSupportEq G H hsupport).symm, ?_⟩
    exact (isOperatorRefutation_map_equiv_of_support_eq H G hconflictH hconflictG hsupport.symm w).mpr hw

/-- The value-one property depends only on the signed support. -/
theorem commutingOperatorValue_eq_one_iff_of_support_eq
    (G H : FiniteFourPlayerXORGame Question)
    (hconflictG : ¬ G.HasConflictingTargets)
    (hconflictH : ¬ H.HasConflictingTargets)
    (hsupport : G.support = H.support) :
    commutingOperatorValue G = 1 ↔ commutingOperatorValue H = 1 := by
  rw [commutingOperatorValue_eq_one_iff_noOperatorRefutation G hconflictG,
    commutingOperatorValue_eq_one_iff_noOperatorRefutation H hconflictH]
  exact Iff.not (hasOperatorRefutation_iff_of_support_eq G H hconflictG hconflictH hsupport)

/-- Existence of a perfect MERP strategy depends only on the signed support. -/
theorem hasPerfectMERPStrategy_iff_of_support_eq
    (G H : FiniteFourPlayerXORGame Question) (hsupport : G.support = H.support) :
    HasPerfectMERPStrategy G ↔ HasPerfectMERPStrategy H := by
  unfold HasPerfectMERPStrategy
  constructor
  · rintro ⟨phase, hphase⟩
    refine ⟨phase, ?_⟩
    intro clause hclause
    exact hphase clause (by rwa [hsupport])
  · rintro ⟨phase, hphase⟩
    refine ⟨phase, ?_⟩
    intro clause hclause
    exact hphase clause (by rwa [← hsupport])

/-- An operator refutation forces the commuting-operator value strictly below
one, with the gap derived from the finite support. -/
theorem commutingOperatorValue_lt_one_of_hasOperatorRefutation
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (href : HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict)) :
    commutingOperatorValue G < 1 :=
  hasOperatorRefutation_implies_commutingOperatorValue_lt_one G hconflict href

/-- The lifted universe-zero strategies realize values in the commuting
correlation value set. -/
theorem liftCommutingStrategy_expectedWin_mem_commutingOperatorValues
    (G : FiniteFourPlayerXORGame Question)
    {Hilbert : Type 0} [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert]
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    expectedWin G (FourPlayerCommutingOperatorStrategy.uliftStrategy strategy) ∈
      commutingOperatorValues G := by
  refine ⟨liftCommutingCorrelation G strategy, ?_⟩
  rfl

end

end XORGame
end QIT

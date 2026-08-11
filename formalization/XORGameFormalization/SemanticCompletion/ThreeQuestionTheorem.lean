/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.OperationalValue
public import XORGameFormalization.SemanticCompletion.QuestionReduction
public import XORGameFormalization.SemanticCompletion.PhaseDuality
public import XORGameFormalization.SemanticCompletion.MERPStrategy
public import XORGameFormalization.Main
public import Mathlib.Tactic

/-!
# The full three-question commuting/MERP theorem

For any finite weighted four-player binary XOR game in which every player has
at most three active questions, a perfect commuting-operator strategy exists
exactly when a perfect MERP strategy exists, and the commuting-operator value
is one exactly under the same condition.  The target-conflict case is handled
explicitly, and the theorem is exposed for indexed clause data with duplicate
or zero weights without any caller preprocessing.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uH uC

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

/-- A perfect commuting-operator strategy forces a perfect MERP strategy when
every player has at most three active questions. -/
theorem perfectCommutingOperatorStrategy_implies_perfectMERP_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) :
    FourPlayerCommutingOperatorStrategy.HasPerfectCommutingOperatorStrategy G →
      HasPerfectMERPStrategy G := by
  intro hperfect
  by_cases hconflict : G.HasConflictingTargets
  · exact False.elim
      (FourPlayerCommutingOperatorStrategy.conflictingTargets_exclude_perfectCommutingOperatorStrategy
        G hconflict hperfect)
  · have hparity : G.IsMERPPerfectParityOnSupport hconflict := by
      by_contra hpar
      have hpref : HasPREF G.reducedQuery (G.reducedSign hconflict) := by
        by_contra hnopref
        exact hpar
          ((isMERPPerfectParity_iff_not_hasPREF (query := G.reducedQuery)
            (sign := G.reducedSign hconflict)).mpr hnopref)
      have href : HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) :=
        FiniteFourPlayerXORGame.operatorRefutation_of_pref_of_activeQuestionBound_le_three
          G hconflict hbound hpref
      rcases hperfect with ⟨model⟩
      letI := model.normedAddCommGroup
      letI := model.innerProductSpace
      letI := model.completeSpace
      have hperf : FourPlayerCommutingOperatorStrategy.IsPerfectCommutingOperatorStrategy
          G.reducedQuery (G.reducedSign hconflict) model.strategy := by
        intro c
        simpa [FiniteFourPlayerXORGame.reducedSignedClause,
          FiniteFourPlayerXORGame.reducedQuery] using
          model.perfect (G.reducedSignedClause hconflict c)
            (G.reducedSignedClause_mem_support hconflict c)
      exact (FourPlayerCommutingOperatorStrategy.operatorRefutation_excludes_perfectCommutingOperatorStrategy
        G.reducedQuery (G.reducedSign hconflict) model.strategy href) hperf
    exact (G.isMERPPerfectParityOnSupport_iff_hasPerfectMERPStrategy hconflict).mp hparity

/-- With at most three active questions per player, the commuting-operator
value is one exactly when a perfect MERP strategy exists. -/
theorem commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) :
    commutingOperatorValue G = 1 ↔ HasPerfectMERPStrategy G := by
  rw [commutingOperatorValue_eq_one_iff_hasPerfectCommutingOperatorStrategy G]
  constructor
  · exact perfectCommutingOperatorStrategy_implies_perfectMERP_of_activeQuestionBound_le_three
      G hbound
  · exact perfectMERP_implies_hasPerfectCommutingOperatorStrategy G

/-- If no perfect MERP strategy exists, the commuting-operator value is
strictly below one. -/
theorem nonMERP_implies_commutingOperatorValue_lt_one_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3)
    (hnon : ¬ HasPerfectMERPStrategy G) :
    commutingOperatorValue G < 1 := by
  have hle : commutingOperatorValue G ≤ 1 := commutingOperatorValue_le_one G
  have hne : commutingOperatorValue G ≠ 1 := by
    intro hval
    exact hnon ((commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three
      G hbound).mp hval)
  exact lt_of_le_of_ne hle hne

/-- A commuting-operator value of one forces a perfect MERP strategy. -/
theorem commutingOperatorValue_eq_one_implies_MERP_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3)
    (hval : commutingOperatorValue G = 1) :
    HasPerfectMERPStrategy G :=
  (commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three
    G hbound).mp hval

/-- When the ambient question type is `Fin 3`, every player has at most three
active questions. -/
theorem activeQuestionBound_le_three_of_question_fin_three
    (G : FiniteFourPlayerXORGame (Fin 3)) :
    G.activeQuestionBound ≤ 3 := by
  rw [G.activeQuestionBound_le_iff]
  intro p
  have hle : (G.activeQuestions p).card ≤ (Finset.univ : Finset (Fin 3)).card := by
    exact Finset.card_le_card (Finset.subset_univ _)
  simpa using hle

/-- The full three-question theorem for arbitrary indexed clause data with
nonnegative normalized weights and an explicit active-question bound. -/
theorem commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_indexed
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    {Question : Type uQ} [Fintype Question] [DecidableEq Question]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (hbound : (FiniteFourPlayerXORGame.ofIndexed query sign weight
      hweight_nonneg hweight_sum_one).activeQuestionBound ≤ 3) :
    commutingOperatorValue
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          hweight_nonneg hweight_sum_one) = 1 ↔
      HasPerfectMERPStrategy
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          hweight_nonneg hweight_sum_one) :=
  commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three
    (FiniteFourPlayerXORGame.ofIndexed query sign weight hweight_nonneg hweight_sum_one)
    hbound

/-- The full three-question theorem specialized to indexed `Fin 3` clause
data with nonnegative weights.  It needs neither an injective clause map nor
distinct clauses, and zero weights require no preprocessing. -/
theorem commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_indexed_fourByThree
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple (Fin 3))
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1) :
    commutingOperatorValue
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          hweight_nonneg hweight_sum_one) = 1 ↔
      HasPerfectMERPStrategy
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          hweight_nonneg hweight_sum_one) :=
  commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_indexed query sign weight
    hweight_nonneg hweight_sum_one
    (activeQuestionBound_le_three_of_question_fin_three _)

/-- The game-level value-one/perfect-MERP conclusion for indexed `Fin 3` data
and the `IsMERPPerfectParity` conclusion for the same indexed clauses are
stated conjunctively.  The two models are not claimed to be definitionally
equal; each conjunct reuses its own already-proved theorem. -/
theorem indexedFourByThree_combined_endpoint
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    {Hilbert : Type uH} [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → FourPlayerQuestionTuple (Fin 3))
    (hquery : Function.Injective query)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_pos : ∀ c, 0 < weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (strategy : FourPlayerBinaryObservableStrategy (Fin 3) Hilbert)
    (hperfect : IsPerfectFourPlayerBinaryObservableStrategy query sign strategy) :
    (commutingOperatorValue
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          (fun c => le_of_lt (hweight_pos c)) hweight_sum_one) = 1 ↔
      HasPerfectMERPStrategy
        (FiniteFourPlayerXORGame.ofIndexed query sign weight
          (fun c => le_of_lt (hweight_pos c)) hweight_sum_one)) ∧
      IsMERPPerfectParity query sign := by
  constructor
  · exact commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_indexed_fourByThree
      query sign weight (fun c => le_of_lt (hweight_pos c)) hweight_sum_one
  · exact perfectFourPlayerBinaryObservableStrategy_implies_merpPerfectParity
      query hquery sign strategy hperfect

end

end XORGame
end QIT

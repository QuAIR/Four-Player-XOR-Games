/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.ThreeQuestionTheorem
public import Mathlib.Tactic

/-!
# Sharp MERP-separation threshold interface

This module states the sharp-threshold interface without
constructing the four-question witness.  A game on `Fin q` may use fewer
questions, so `q` is an upper bound on the number of active questions per
player.

The witness construction supplies a term of type
`HasMERPSeparationAtMost 4`:

```lean
#check four_isSharpMERPSeparationThreshold_of_witness
```
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

noncomputable section

/-- A game on at most `q` questions whose commuting-operator value is one but
which has no perfect MERP strategy. -/
def HasMERPSeparationAtMost (q : ℕ) : Prop :=
  ∃ G : FiniteFourPlayerXORGame (Fin q),
    commutingOperatorValue G = 1 ∧ ¬ HasPerfectMERPStrategy G

/-- `q` is the sharp threshold when separation occurs at most `q` and no
separation occurs below `q`. -/
def IsSharpMERPSeparationThreshold (q : ℕ) : Prop :=
  HasMERPSeparationAtMost q ∧
    ∀ k < q, ¬ HasMERPSeparationAtMost k

/-- Every game on `Fin q` has active question bound at most `q`. -/
theorem activeQuestionBound_le_of_question_fin (q : ℕ)
    (G : FiniteFourPlayerXORGame (Fin q)) :
    G.activeQuestionBound ≤ q := by
  rw [G.activeQuestionBound_le_iff]
  intro p
  have hle : (G.activeQuestions p).card ≤ (Finset.univ : Finset (Fin q)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  simpa using hle

/-- No game on at most three questions per player can separate the
commuting-operator value from the MERP value. -/
theorem noMERPSeparationAtMost_of_le_three {q : ℕ} (hq : q ≤ 3) :
    ¬ HasMERPSeparationAtMost q := by
  rintro ⟨G, hval, hnon⟩
  have hboundq : G.activeQuestionBound ≤ q := activeQuestionBound_le_of_question_fin q G
  have hbound : G.activeQuestionBound ≤ 3 := le_trans hboundq hq
  exact hnon
    ((commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three
      G hbound).mp hval)

/-- A four-question separation witness makes four the sharp threshold. -/
theorem four_isSharpMERPSeparationThreshold_of_witness
    (hfour : HasMERPSeparationAtMost 4) :
    IsSharpMERPSeparationThreshold 4 := by
  constructor
  · exact hfour
  · intro k hk
    have hk3 : k ≤ 3 := Nat.le_of_lt_succ hk
    exact noMERPSeparationAtMost_of_le_three hk3

end

end XORGame
end QIT

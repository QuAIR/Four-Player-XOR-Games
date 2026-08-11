/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ziao Tang, Chengkai Zhu, Ge Bai, Xin Wang, Ranyiliu Chen
-/

import QIT
import XORGameFormalization.SemanticCompletion.ThreeQuestionTheorem
import XORGameFormalization.V4Witness
import FourXOR.TranslationMatchingClassification
import FourXOR.AllLengthF2

/-!
# Formalization accompanying the four-player XOR-game threshold theorem

This is the public entrypoint for the formal development accompanying
*A Sharp Local-Question Threshold for GHZ-Equatorial Strategies in
Four-Player XOR Games*.

The reusable quantum-information infrastructure is imported from the pinned
`QIT` package provided by QuAIR/Lean-QIT.  The local modules prove the
four-player three-question lifting result, the Klein four-group witness, the
finite-group translation-matching classification, and the elementary-abelian
all-length obstruction.
-/

@[expose] public section

namespace QIT.XORGame

universe uE

noncomputable section

/-- Paper-facing form of obstruction-space exactness for a distinct support
of four-player clauses with three questions per player. -/
theorem obstructionSpaces_eq_fourByThree
    {E : Type uE} [Fintype E] [DecidableEq E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query) :
    refutationParitySpace query = integerRelationParitySpace query := by
  exact paritySpaces_eq_of_everyIntegerRelationHasBalancedLift query
    (everyIntegerRelationHasBalancedLift_of_primitiveCircuits query
      (primitiveCircuit_lifts_fourByThree query hquery))

end

end QIT.XORGame

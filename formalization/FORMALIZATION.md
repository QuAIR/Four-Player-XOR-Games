# Manuscript-to-Lean correspondence

The table records the closest principal declaration for each numbered
mathematical statement.  “Direct” means that the Lean declaration states the
manuscript conclusion, up to notation and packaging.  “Supporting” identifies
a conditional component or a consequence sufficient for a downstream direct
result.  “Alternative route” means that Lean proves the paper's application by
a specialized combinatorial argument rather than formalizing the labeled
general statement itself.

| Manuscript label | Lean declaration(s) | Status |
|---|---|---|
| `thm:main` (i) | `QIT.XORGame.commutingOperatorValue_eq_one_iff_hasPerfectMERP_of_activeQuestionBound_le_three` | Direct |
| `thm:main` (ii) | `QIT.XORGame.v4_value_one`; `QIT.XORGame.v4_no_MERP`; `QIT.XORGame.v4_separation_at_most_4` | Direct |
| sharp threshold in `thm:main` | `QIT.XORGame.four_is_sharp_threshold` | Direct |
| `prop:weight-reduction` | `QIT.XORGame.commutingOperatorValue_eq_one_iff_of_support_eq`; `QIT.XORGame.weightedValue_lt_one_of_uniformValue_lt_one` | Partial: value-one/support consequences and the lower-weight strict-gap implication; the displayed `p_max` inequality is not directly formalized |
| `thm:exact-circuit-lifting` | `QIT.XORGame.primitiveCircuit_lifts_fourByThree` | Supporting consequence: parity lift only; exact multiplicities and `y(w_c) = ±c` are not stated by this declaration |
| `cor:obstruction-exactness` | `QIT.XORGame.obstructionSpaces_eq_fourByThree` | Direct |
| `lem:alternating-lift` | `QIT.XORGame.balancedWord_alternatingLift_isIntegerRelation`; `QIT.XORGame.alternatingLift_mod_two` | Direct |
| `prop:circuit-generation` | `QIT.XORGame.primitiveCircuits_closure_eq_kernel`; `QIT.XORGame.everyIntegerRelationHasBalancedLift_of_primitiveCircuits` | Direct for the generation and downstream parity assembly |
| `lem:no-singleton-block` | `QIT.XORGame.fullCircuit_questionFiber_card_ne_one` | Direct |
| `prop:rank-cap` | `QIT.XORGame.fullRationalCircuit_card_eq_rank_add_one`; `QIT.XORGame.rationalIncidence_rank_le_usedQuestions`; `QIT.XORGame.fourByThree_primitiveCircuit_card_le_ten`; `QIT.XORGame.tenClause_primitiveIncidenceCircuit_uses_all_questions`; `QIT.XORGame.nineClause_primitiveIncidenceCircuit_has_at_most_one_nonternary_player` | Direct across the rank, cutoff, and boundary-profile declarations |
| `lem:exact-multiplicity` | `QIT.XORGame.parityPairing_occurrenceParity`; `QIT.XORGame.exactMultiplicityBalancedLift_hasBalancedLift` | Supporting only; the conclusion `y(w) = ±c` is not directly formalized |
| `lem:ordering` | `QIT.XORGame.InvolutionWord.reducesToEmpty_of_toFinset_card_le_two_of_alternatingSum_zero`; `QIT.XORGame.exists_bipartiteLinearForestAlternatingLayout` | Direct |
| `prop:selected-block` | `QIT.XORGame.selectedBlockLinearForest_exactMultiplicityBalancedLift` | Direct |
| `prop:three-color` | `QIT.XORGame.threeColor_colorwiseMatching_linearForest` | Direct |
| `prop:four-singleton` | `QIT.XORGame.ColorSignatureSystem.linearForestMatching_of_singleton` | Direct |
| `prop:four-ternary-reduction` | `QIT.XORGame.hasExactMultiplicityBalancedLift_of_ternaryPlayers_card_le_three` | Direct |
| `lem:separation-packing` | `QIT.XORGame.safeCenters_card_le_six_of_even_separated`; `QIT.XORGame.evenSupportDistances_separated_of_sharedBlockMissingCell_escape` | Direct for the packing bound; the second declaration is a conditional escape interface |
| `lem:safe-excess` | `QIT.XORGame.safeHole_neighborhood_excess` | Direct |
| `prop:subnine` | `QIT.XORGame.atMostEight_exactLift_of_nonliftable_even_separated` | Supporting conditional component, not the unconditional manuscript proposition |
| `lem:nine-independence` | `QIT.XORGame.nineBallCover_rationalIncidence_linearIndependent` | Direct |
| `prop:nine` | `QIT.XORGame.nineClause_exactLift_of_nonliftable_even_separated` | Supporting conditional component, not the unconditional manuscript proposition |
| `prop:ten-noncover` | `QIT.XORGame.tenClause_noncovering_geometry_impossible` | Supporting conditional contradiction, not the liftability statement itself |
| `prop:ten-cover` | `QIT.XORGame.tenBallCover_structural_contradiction`; `QIT.XORGame.tenBallCover_not_fullRationalCircuit` | Supporting structural components |
| `thm:cayley-cyclic` | `QIT.Research.FourXOR.hasCommonNoncrossingOrder_iff_isCyclic`; `QIT.Research.FourXOR.cyclic_cayley_has_true_refutation` | Direct for the matching classification; partial for the each-clause-once refutation equivalence |
| `lem:cayley-chord` | `QIT.Research.FourXOR.NestedWord.equalPairs_noncrossing`; `QIT.Research.FourXOR.NestedWord.reducible` | One-way supporting results under the stronger `NestedWord` hypothesis; the stated iff is not directly formalized |
| `lem:cayley-side` | `QIT.Research.FourXOR.same_side` | Direct |
| `lem:cayley-generator` | `QIT.Research.FourXOR.S_succ_dj_eq_d`; `QIT.Research.FourXOR.S_pow`; `QIT.Research.FourXOR.noncrossing_order_cyclic` | Direct for the power-set conclusion and cyclicity, with the constant-`d_j` induction step exposed as a supporting declaration |
| `lem:even-subgroup` | reduction interfaces in `FourXOR.AllLength` and `FourXOR.AllLengthGame` | Alternative route: specialized deletion invariants; the free-generation statement is not formalized |
| `lem:magnus-conditions` | `QIT.Research.FourXOR.altSum_reducible`; `QIT.Research.FourXOR.pairSum_reducible` | Alternative route: specialized reducible-word invariants; the general Magnus lemma is not formalized |
| elementary-abelian conclusion in `sec:magnus` | `QIT.Research.FourXOR.cayley_f2r_hasPREF_and_no_refutation` | Direct |

## Dependency boundary

The project begins with `import QIT`.  QuAIR/Lean-QIT supplies reusable
quantum-information definitions and operator infrastructure and imports
Mathlib.  All files specific to the circuit-lifting and Cayley-game arguments
are part of this repository.  The Lake configuration pins the exact QIT
revision and the manifest pins the complete transitive dependency graph.

The formalization contains no proof placeholders and no manually declared
axioms.  The repository test suite runs `#print axioms` on the paper-facing
declarations.  It accepts only `propext`, `Classical.choice`, and `Quot.sound`,
plus seven individually enumerated `native_decide` bridge axioms inherited by
the finite cardinality and Hamming-space computations in the three-question
proof.  The V4, translation-matching, and elementary-abelian declarations
depend only on the three standard axioms.

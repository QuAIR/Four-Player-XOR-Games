/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import XORGameFormalization.SemanticCompletion.SharpThresholdInterface
import XORGameFormalization.SemanticCompletion.ThreeQuestionTheorem
import XORGameFormalization.SemanticCompletion.PhaseDuality
import XORGameFormalization.SemanticCompletion.QuestionReduction
import FourXOR.AllLengthF2
import Mathlib.Tactic

/-!
# The four-question witness: the Klein four-group Cayley game

This module constructs the four-question witness
`HasMERPSeparationAtMost 4` for the sharp-threshold result.  The game is the
Cayley game of `V4 = F_2^2` with four players and four questions: clauses
`E_x` (every player receives `x`) and `O_x` (player `α` receives `x + α`),
each of weight `1/8`.  The proofs establish

- the game has no conflicting targets;
- it has a PREF (the standard `-1` on `E`, `+1` on `O`), hence no perfect
  MERP strategy;
- it has no operator refutation (the transported all-length obstruction for
  `F_2^2`), hence commuting-operator value one.

Combining these gives `HasMERPSeparationAtMost 4`.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

noncomputable section

/-- The Klein four-group elements encoded as `Fin 4`:
`0=(0,0)`, `1=(0,1)`, `2=(1,0)`, `3=(1,1)`. -/
def v4Bits (x : Fin 4) : ZMod 2 × ZMod 2 :=
  (if x = 2 ∨ x = 3 then 1 else 0, if x = 1 ∨ x = 3 then 1 else 0)

/-- Reconstruct a `Fin 4` element from its two bits. -/
def v4OfBits (a b : ZMod 2) : Fin 4 :=
  if a = 0 then (if b = 0 then 0 else 1) else (if b = 0 then 2 else 3)

/-- Klein-four addition on `Fin 4` by an explicit case table. -/
def v4add (x y : Fin 4) : Fin 4 :=
  ⟨match x.val, y.val with
   | 0, n => n
   | n, 0 => n
   | 1, 1 => 0
   | 1, 2 => 3
   | 1, 3 => 2
   | 2, 1 => 3
   | 2, 2 => 0
   | 2, 3 => 1
   | 3, 1 => 2
   | 3, 2 => 1
   | 3, 3 => 0
   | _, _ => 0, by
     fin_cases x <;> fin_cases y <;> norm_num⟩

@[simp] theorem v4Bits_zero : v4Bits (0 : Fin 4) = (0, 0) := by
  simp [v4Bits]

@[simp] theorem v4Bits_one : v4Bits (1 : Fin 4) = (0, 1) := by
  simp [v4Bits, Fin.ext_iff]

@[simp] theorem v4Bits_two : v4Bits (2 : Fin 4) = (1, 0) := by
  simp [v4Bits, Fin.ext_iff]

@[simp] theorem v4Bits_three : v4Bits (3 : Fin 4) = (1, 1) := by
  simp [v4Bits, Fin.ext_iff]

@[simp] theorem v4OfBits_zero_zero : v4OfBits 0 0 = (0 : Fin 4) := by
  rfl

theorem v4add_zero_left (x : Fin 4) : v4add 0 x = x := by
  fin_cases x <;> decide

theorem v4add_zero_right (x : Fin 4) : v4add x 0 = x := by
  fin_cases x <;> decide

theorem v4add_comm (x y : Fin 4) : v4add x y = v4add y x := by
  fin_cases x <;> fin_cases y <;> decide

theorem v4add_assoc (x y z : Fin 4) : v4add (v4add x y) z = v4add x (v4add y z) := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    decide

theorem v4add_right_cancel {x y z : Fin 4} (h : v4add x y = v4add x z) : y = z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;>
    (try contradiction) <;> decide

theorem v4add_one_ne (x : Fin 4) : v4add x 1 ≠ x := by
  fin_cases x <;> decide

/-- The equivalence between `Fin 4` and the pointwise bit functions. -/
def fin4EquivFun2 : Fin 4 ≃ (Fin 2 → ZMod 2) where
  toFun x := fun i => if i = 0 then (v4Bits x).1 else (v4Bits x).2
  invFun f := v4OfBits (f 0) (f 1)
  left_inv := by
    intro x
    fin_cases x <;> simp [v4Bits, v4OfBits, Fin.ext_iff]
  right_inv := by
    intro f
    funext i
    fin_cases i
    · rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (f 0) with h0 | h0 <;>
      rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (f 1) with h1 | h1 <;>
      simp [v4Bits, v4OfBits, h0, h1]
    · rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (f 0) with h0 | h0 <;>
      rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one (f 1) with h1 | h1 <;>
      simp [v4Bits, v4OfBits, h0, h1]

theorem v4add_eq_pointwise (x y : Fin 4) :
    v4add x y = fin4EquivFun2.symm (fin4EquivFun2 x + fin4EquivFun2 y) := by
  apply fin4EquivFun2.injective
  funext i
  fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [v4add, v4Bits, v4OfBits, fin4EquivFun2] <;> decide

/-- The eight clause indices of the V4 Cayley game. -/
abbrev V4Clause := Fin 4 × Bool

/-- The unsigned query tuple of a V4 clause. -/
def v4Query (c : V4Clause) : FourPlayerQuestionTuple (Fin 4) :=
  if c.2 then fun p => v4add c.1 p else fun _ => c.1

/-- The target sign: only `O_0` carries bit one. -/
def v4Sign (c : V4Clause) : ZMod 2 :=
  if c.2 ∧ c.1 = 0 then 1 else 0

/-- Uniform weight `1/8` on every clause. -/
def v4Weight (c : V4Clause) : ℝ := 1 / 8

theorem v4Weight_nonneg : ∀ c : V4Clause, 0 ≤ v4Weight c := by
  intro c
  simp [v4Weight]

theorem v4Weight_sum_one : (∑ c : V4Clause, v4Weight c) = 1 := by
  simp [v4Weight, Finset.sum_const, Fintype.card_prod, Fintype.card_fin]

/-- The V4 Cayley game as a finite four-player XOR game on four questions. -/
noncomputable def v4Game : FiniteFourPlayerXORGame (Fin 4) :=
  FiniteFourPlayerXORGame.ofIndexed v4Query v4Sign v4Weight
    v4Weight_nonneg v4Weight_sum_one

@[simp] theorem v4Query_E (x : Fin 4) : v4Query (x, false) = (fun _ : Fin 4 => x) := by
  simp [v4Query]

@[simp] theorem v4Query_O (x : Fin 4) : v4Query (x, true) = (fun p : Fin 4 => v4add x p) := by
  simp [v4Query]

@[simp] theorem v4Sign_E (x : Fin 4) : v4Sign (x, false) = (0 : ZMod 2) := by
  simp [v4Sign]

@[simp] theorem v4Sign_O_zero : v4Sign (0, true) = (1 : ZMod 2) := by
  simp [v4Sign]

@[simp] theorem v4Sign_O_ne_zero {x : Fin 4} (hx : x ≠ 0) : v4Sign (x, true) = (0 : ZMod 2) := by
  simp [v4Sign, hx]

theorem v4Query_E_ne_O (x y : Fin 4) :
    (fun _ : Fin 4 => x) ≠ (fun p : Fin 4 => v4add y p) := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have hy0 : v4add y 0 = y := v4add_zero_right y
  have hx_eq_y : x = y := by
    simpa [hy0] using h0
  have hx1 : v4add y 1 = y := by
    simpa [hx_eq_y] using h1.symm
  exact (v4add_one_ne y) (by simpa [hx_eq_y] using hx1)

theorem v4Query_injective : Function.Injective v4Query := by
  intro c d h
  rcases c with ⟨x, hc⟩ <;> rcases d with ⟨y, hd⟩ <;> cases hc <;> cases hd
  · -- E x = E y
    have hxy := congrFun h 0
    simp at hxy
    simp [hxy]
  · -- E x = O y
    exact False.elim (v4Query_E_ne_O x y (by simpa using h))
  · -- O x = E y
    exact False.elim (v4Query_E_ne_O y x (by simpa [eq_comm] using h))
  · -- O x = O y
    have hxy := congrFun h 0
    simp [v4add_zero_right] at hxy
    simp [hxy]

/-- The aggregated weight of a signed tuple is `1/8` times the number of
matching clause indices. -/
theorem v4Game_weight_eq (q : FourPlayerQuestionTuple (Fin 4)) (b : ZMod 2) :
    v4Game.weight (q, b) =
      (1 / 8 : ℝ) *
        (Finset.univ.filter (fun c : V4Clause =>
          v4Query c = q ∧ v4Sign c = b)).card := by
  rw [v4Game, FiniteFourPlayerXORGame.ofIndexed_weight]
  rw [← Finset.sum_filter]
  simp [v4Weight, Finset.sum_const, nsmul_eq_mul]
  ring

/-- A signed tuple has positive weight iff it is one of the eight clauses. -/
theorem v4Game_weight_pos_iff (q : FourPlayerQuestionTuple (Fin 4)) (b : ZMod 2) :
    0 < v4Game.weight (q, b) ↔
      ∃ c : V4Clause, v4Query c = q ∧ v4Sign c = b := by
  rw [v4Game_weight_eq]
  constructor
  · intro hpos
    by_contra hnone
    have hcard : (Finset.univ.filter (fun c : V4Clause =>
        v4Query c = q ∧ v4Sign c = b)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro c hc
      exact hnone ⟨c, (Finset.mem_filter.mp hc).2⟩
    simp [hcard] at hpos
  · rintro ⟨c, hq, hs⟩
    have hmem : c ∈ Finset.univ.filter (fun c : V4Clause =>
        v4Query c = q ∧ v4Sign c = b) := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, ⟨hq, hs⟩⟩
    have hcard : 0 < (Finset.univ.filter (fun c : V4Clause =>
        v4Query c = q ∧ v4Sign c = b)).card :=
      Finset.card_pos.mpr ⟨c, hmem⟩
    have hpos : 0 < (1 / 8 : ℝ) := by norm_num
    have hcardR : (0 : ℝ) <
        (Finset.univ.filter (fun c : V4Clause =>
          v4Query c = q ∧ v4Sign c = b)).card := by
      exact_mod_cast hcard
    nlinarith

/-- The V4 game has no conflicting targets. -/
theorem v4_no_conflict : ¬ v4Game.HasConflictingTargets := by
  rintro ⟨q, h0, h1⟩
  rcases (v4Game_weight_pos_iff q 1).1 h1 with ⟨c1, hq1, hs1⟩
  rcases c1 with ⟨x1, b1⟩
  have htrue : b1 = true := by
    by_cases hb : b1
    · exact hb
    · simp [v4Sign, hb] at hs1
  have hzero : x1 = 0 := by
    by_cases hz : x1 = 0
    · exact hz
    · simp [v4Sign, htrue, hz] at hs1
  have hq_id : q = (fun p : Fin 4 => p) := by
    simpa [hzero, htrue, v4Query_O, v4add_zero_left] using hq1.symm
  rcases (v4Game_weight_pos_iff q 0).1 h0 with ⟨c0, hq0, hs0⟩
  rcases c0 with ⟨x0, b0⟩
  by_cases hb0 : b0
  · have hxne : x0 ≠ 0 := by
      intro hx
      simp [v4Sign, hb0, hx] at hs0
    have hqO : q = (fun p : Fin 4 => v4add x0 p) := by
      simpa [hb0] using hq0.symm
    have hz := congrFun (hq_id.symm.trans hqO) 0
    have : x0 = 0 := by
      simpa [v4add_zero_right, eq_comm] using hz
    exact hxne this
  · have hqE : q = (fun _ : Fin 4 => x0) := by
      simpa [hb0] using hq0.symm
    have hc : (fun p : Fin 4 => p) ≠ (fun _ : Fin 4 => x0) := by
      intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      have : (0 : Fin 4) = 1 := by
        simpa using h0.trans h1.symm
      norm_num at this
    exact hc (hq_id.symm.trans hqE)

theorem v4add_add_self (x y : Fin 4) : v4add (v4add x y) y = x := by
  fin_cases x <;> fin_cases y <;> decide

noncomputable def v4ReducedClause (hconflict : ¬ v4Game.HasConflictingTargets)
    (c : v4Game.ReducedClauseId) : V4Clause :=
  Classical.choose
    ((v4Game_weight_pos_iff c.1 (v4Game.reducedSign hconflict c)).1
      (v4Game.reducedSign_supported hconflict c))

theorem v4ReducedClause_spec (hconflict : ¬ v4Game.HasConflictingTargets)
    (c : v4Game.ReducedClauseId) :
    v4Query (v4ReducedClause hconflict c) = c.1 ∧
      v4Sign (v4ReducedClause hconflict c) = v4Game.reducedSign hconflict c :=
  Classical.choose_spec
    ((v4Game_weight_pos_iff c.1 (v4Game.reducedSign hconflict c)).1
      (v4Game.reducedSign_supported hconflict c))

theorem v4Clause_unique {q : FourPlayerQuestionTuple (Fin 4)} {b : ZMod 2}
    {c1 c2 : V4Clause}
    (h1 : v4Query c1 = q ∧ v4Sign c1 = b)
    (h2 : v4Query c2 = q ∧ v4Sign c2 = b) : c1 = c2 :=
  v4Query_injective (h1.1.trans h2.1.symm)

noncomputable def v4ReducedClauseInv (c : V4Clause) : v4Game.ReducedClauseId :=
  ⟨v4Query c, ⟨v4Sign c,
    (v4Game_weight_pos_iff (v4Query c) (v4Sign c)).2 ⟨c, rfl, rfl⟩⟩⟩

/-- The reduced clause ids of the V4 game are exactly its eight clause
indices. -/
noncomputable def v4ReducedEquiv (hconflict : ¬ v4Game.HasConflictingTargets) :
    V4Clause ≃ v4Game.ReducedClauseId where
  toFun := v4ReducedClauseInv
  invFun := v4ReducedClause hconflict
  left_inv := by
    intro c
    apply v4Clause_unique (b := v4Sign c)
    · have hsign : v4Game.reducedSign hconflict (v4ReducedClauseInv c) = v4Sign c := by
        exact (v4Game.reducedSign_unique hconflict (v4ReducedClauseInv c)
          (b := v4Sign c)
          (by
            simpa [v4ReducedClauseInv] using
              (v4Game_weight_pos_iff (v4Query c) (v4Sign c)).2 ⟨c, rfl, rfl⟩)).symm
      constructor
      · simpa [v4ReducedClauseInv] using
          (v4ReducedClause_spec hconflict (v4ReducedClauseInv c)).1
      · simpa [hsign] using
          (v4ReducedClause_spec hconflict (v4ReducedClauseInv c)).2
    · constructor <;> rfl
  right_inv := by
    intro c
    apply Subtype.ext
    exact (v4ReducedClause_spec hconflict c).1

lemma sum_reduced_eq_sum_clause (hconflict : ¬ v4Game.HasConflictingTargets)
    {M : Type*} [AddCommMonoid M] (f : v4Game.ReducedClauseId → M) :
    (∑ c : v4Game.ReducedClauseId, f c) = ∑ c : V4Clause, f (v4ReducedEquiv hconflict c) := by
  rw [← Equiv.sum_comp (v4ReducedEquiv hconflict) f]

/-- The standard `-1` on `E`, `+1` on `O` PREF witness on reduced clauses. -/
noncomputable def v4PrefY (hconflict : ¬ v4Game.HasConflictingTargets)
    (c : v4Game.ReducedClauseId) : ℤ :=
  if (v4ReducedClause hconflict c).2 then 1 else -1

theorem v4PrefY_zmod (hconflict : ¬ v4Game.HasConflictingTargets)
    (c : v4Game.ReducedClauseId) : ((v4PrefY hconflict c : ℤ) : ZMod 2) = 1 := by
  by_cases hb : (v4ReducedClause hconflict c).2
  · simp [v4PrefY, hb]
  · have hneg : ((-1 : ℤ) : ZMod 2) = 1 := by decide
    simp [v4PrefY, hb, hneg]

theorem v4PrefY_clause (hconflict : ¬ v4Game.HasConflictingTargets) (c : V4Clause) :
    v4PrefY hconflict (v4ReducedEquiv hconflict c) = if c.2 then 1 else -1 := by
  change (if (v4ReducedClause hconflict (v4ReducedClauseInv c)).2 then 1 else -1) =
    (if c.2 = true then 1 else -1)
  have h := (v4ReducedEquiv hconflict).left_inv c
  have h' : v4ReducedClause hconflict (v4ReducedClauseInv c) = c := by
    simpa [v4ReducedEquiv] using h
  rw [h']

theorem v4ReducedQuery_eq (hconflict : ¬ v4Game.HasConflictingTargets) (c : V4Clause) :
    v4Game.reducedQuery (v4ReducedEquiv hconflict c) = v4Query c := by
  simp [v4ReducedEquiv, v4ReducedClauseInv, FiniteFourPlayerXORGame.reducedQuery]

theorem v4sum_E (q : Fin 4) :
    (∑ x : Fin 4, -(if x = q then (1 : ℤ) else 0)) = -1 := by
  rw [Finset.sum_eq_single q]
  · simp
  · intro b hb hbne
    simp [hbne]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ q))

theorem v4sum_O (p q : Fin 4) :
    (∑ x : Fin 4, (if v4add x p = q then (1 : ℤ) else 0)) = 1 := by
  let a : Fin 4 := v4add q p
  rw [Finset.sum_eq_single a]
  · have h : v4add (v4add q p) p = q := by
      fin_cases q <;> fin_cases p <;> decide
    simp [a, h]
  · intro b hb hbne
    have hbq : v4add b p ≠ q := by
      intro hbq
      apply hbne
      have hL : v4add (v4add b p) p = v4add q p := congrArg (fun z => v4add z p) hbq
      rw [v4add_add_self] at hL
      exact hL
    simp [hbq]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ a))

theorem v4PrefY_integerRelation (hconflict : ¬ v4Game.HasConflictingTargets) :
    IsIntegerRelation v4Game.reducedQuery (v4PrefY hconflict) := by
  intro pq
  rcases pq with ⟨p, q⟩
  rw [sum_reduced_eq_sum_clause hconflict]
  simp [incidence, v4ReducedQuery_eq hconflict, v4PrefY_clause hconflict]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [add_comm]
  rw [Finset.sum_add_distrib]
  rw [v4sum_E, v4sum_O]
  simp

theorem v4PrefY_odd (hconflict : ¬ v4Game.HasConflictingTargets) :
    parityPairing (v4Game.reducedSign hconflict) (relationParity (v4PrefY hconflict)) = 1 := by
  change (∑ c : v4Game.ReducedClauseId,
    v4Game.reducedSign hconflict c * ((v4PrefY hconflict c : ℤ) : ZMod 2)) = 1
  rw [sum_reduced_eq_sum_clause hconflict]
  have hsign : ∀ c : V4Clause,
      v4Game.reducedSign hconflict (v4ReducedEquiv hconflict c) = v4Sign c := by
    intro c
    have hpos : 0 < v4Game.weight (v4Query c, v4Sign c) :=
      (v4Game_weight_pos_iff (v4Query c) (v4Sign c)).2 ⟨c, rfl, rfl⟩
    have hpos' : 0 < v4Game.weight ((v4ReducedEquiv hconflict c).1, v4Sign c) := by
      simpa [v4ReducedEquiv, v4ReducedClauseInv] using hpos
    exact (v4Game.reducedSign_unique hconflict (v4ReducedEquiv hconflict c)
      (b := v4Sign c) hpos').symm
  have hsum : (∑ c : V4Clause,
      v4Game.reducedSign hconflict (v4ReducedEquiv hconflict c) *
        ((v4PrefY hconflict (v4ReducedEquiv hconflict c) : ℤ) : ZMod 2)) =
      ∑ c : V4Clause, v4Sign c := by
    apply Finset.sum_congr rfl
    intro c hc
    simp [hsign c, v4PrefY_zmod hconflict (v4ReducedEquiv hconflict c)]
  rw [hsum]
  rw [← Finset.univ_product_univ, Finset.sum_product]
  simp [v4Sign, add_comm]
  decide

/-- The standard `-1`/`+1` assignment is a PREF for the V4 game. -/
theorem v4_has_pref (hconflict : ¬ v4Game.HasConflictingTargets) :
    HasPREF v4Game.reducedQuery (v4Game.reducedSign hconflict) :=
  ⟨v4PrefY hconflict, ⟨v4PrefY_integerRelation hconflict, v4PrefY_odd hconflict⟩⟩

/-- The V4 game has no perfect MERP strategy. -/
theorem v4_no_MERP (hconflict : ¬ v4Game.HasConflictingTargets) :
    ¬ HasPerfectMERPStrategy v4Game := by
  intro h
  have hpar : v4Game.IsMERPPerfectParityOnSupport hconflict :=
    (v4Game.isMERPPerfectParityOnSupport_iff_hasPerfectMERPStrategy hconflict).2 h
  have hnopref : ¬ HasPREF v4Game.reducedQuery (v4Game.reducedSign hconflict) :=
    (isMERPPerfectParity_iff_not_hasPREF v4Game.reducedQuery
      (v4Game.reducedSign hconflict)).1 hpar
  exact hnopref (v4_has_pref hconflict)

/-- An `InvolutionWord.ReducesToEmpty` certificate supplies an explicit
adjacent-pair deletion sequence. -/
lemma reducesToEmpty_reducible {α : Type*} {l : List α}
    (h : InvolutionWord.ReducesToEmpty l) : QIT.Research.FourXOR.Reducible l := by
  induction h with
  | nil =>
      exact Relation.ReflTransGen.refl
  | insert left right a reduced ih =>
      have hstep : QIT.Research.FourXOR.Step
          (left ++ a :: a :: right) (left ++ right) :=
        ⟨left, right, a, by simp, rfl⟩
      exact Relation.ReflTransGen.trans (Relation.ReflTransGen.single hstep) ih

/-- A deletion step is transported by any letter map. -/
lemma step_map {α β : Type*} (f : α → β) {w w' : List α}
    (h : QIT.Research.FourXOR.Step w w') :
    QIT.Research.FourXOR.Step (w.map f) (w'.map f) := by
  rcases h with ⟨l, r, a, hw, hw'⟩
  refine ⟨l.map f, r.map f, f a, ?_, ?_⟩
  · rw [hw]
    simp [List.map_append]
  · rw [hw']
    simp [List.map_append]

/-- Free reduction is transported by any letter map. -/
lemma reducible_map {α β : Type*} {l : List α} (f : α → β)
    (h : QIT.Research.FourXOR.Reducible l) : QIT.Research.FourXOR.Reducible (l.map f) := by
  exact Relation.ReflTransGen.lift (List.map f) (fun a b hstep => step_map f hstep) h

/-- The Klein four group as an equivalence between `Fin 4` and its two-bit
representation. -/
noncomputable def v4EquivZ2 : Fin 4 ≃ (ZMod 2 × ZMod 2) where
  toFun := v4Bits
  invFun := fun p => v4OfBits p.1 p.2
  left_inv := by
    intro x
    fin_cases x <;> decide
  right_inv := by
    intro p
    rcases p with ⟨a, b⟩
    rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one a with ha0 | ha0 <;>
      rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one b with hb0 | hb0 <;>
      simp [v4Bits, v4OfBits, ha0, hb0]

theorem v4add_eq_add (x y : Fin 4) : v4Bits (v4add x y) = v4Bits x + v4Bits y := by
  fin_cases x <;> fin_cases y <;> decide

@[simp] theorem v4Bits_eq_zero {x : Fin 4} : v4Bits x = 0 ↔ x = 0 := by
  constructor
  · intro h
    fin_cases x <;> simp [v4Bits] at h ⊢
  · intro h
    subst x
    simp [v4Bits]

theorem v4Query_eq_letter (c : V4Clause) (p : Fin 4) :
    v4Bits (v4Query c p) =
      QIT.Research.FourXOR.letterG (v4Bits c.1, c.2) (v4Bits p) := by
  by_cases hb : c.2
  · simp [v4Query, hb, QIT.Research.FourXOR.letterG, v4add_eq_add]
  · simp [v4Query, hb, QIT.Research.FourXOR.letterG]

lemma zmod2_sum_eq_count_one (l : List (ZMod 2)) :
    l.sum = (l.count (1 : ZMod 2) : ZMod 2) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases ha : a = 1
      · simp [ha, ih, add_comm]
      · rcases FiniteFourPlayerXORGame.zmodTwo_eq_zero_or_one a with ha0 | ha1
        · simp [ha0, ih]
        · exact False.elim (ha ha1)

lemma count_map_eq_countP {α : Type*} (l : List α) (f : α → ZMod 2) :
    (l.map f).count (1 : ZMod 2) = l.countP (fun c => f c = 1) := by
  induction l with
  | nil => simp
  | cons a t ih =>
      by_cases h : f a = 1 <;> simp [h, ih]

theorem v4Sign_eq_one_iff (c : V4Clause) : v4Sign c = 1 ↔ c.2 = true ∧ c.1 = 0 := by
  by_cases hb : c.2
  · by_cases hz : c.1 = 0
    · simp [v4Sign, hb, hz]
    · simp [v4Sign, hb, hz]
  · simp [v4Sign, hb]

lemma countP_indicator_eq_count {α : Type*} (w : List α) (P : α → Prop)
    [DecidablePred P] :
    QIT.Research.FourXOR.countP w P =
      (w.map (fun a => if P a then (1 : ZMod 2) else 0)).count 1 := by
  induction w with
  | nil => simp [QIT.Research.FourXOR.countP]
  | cons a t ih =>
      by_cases h : P a
      · have hdec : decide (P a) = true := decide_eq_true h
        simp [QIT.Research.FourXOR.countP, hdec, h, add_comm]
        change QIT.Research.FourXOR.countP t P =
          List.count 1 (List.map (fun a => if P a then (1 : ZMod 2) else 0) t)
        exact ih
      · have hdec : decide (P a) = false := decide_eq_false h
        simp [QIT.Research.FourXOR.countP, hdec, h]
        change QIT.Research.FourXOR.countP t P =
          List.count 1 (List.map (fun a => if P a then (1 : ZMod 2) else 0) t)
        exact ih

theorem v4_no_operator_refutation (hconflict : ¬ v4Game.HasConflictingTargets) :
    ¬ HasOperatorRefutation v4Game.reducedQuery (v4Game.reducedSign hconflict) := by
  rintro ⟨word, hbal, hpar⟩
  let wV : List V4Clause := word.map (v4ReducedEquiv hconflict |>.symm)
  let wG : List (QIT.Research.FourXOR.GameClause (ZMod 2 × ZMod 2)) :=
    wV.map (fun c => (v4Bits c.1, c.2))
  have hred : ∀ α : ZMod 2 × ZMod 2,
      QIT.Research.FourXOR.Reducible (QIT.Research.FourXOR.projectionG wG α) := by
    intro α
    let p : Fin 4 := v4EquivZ2.symm α
    have hα : v4Bits p = α := v4EquivZ2.apply_symm_apply α
    have hq : ∀ c : v4Game.ReducedClauseId,
        v4Game.reducedQuery c = v4Query (v4ReducedEquiv hconflict |>.symm c) := by
      intro c
      simpa [v4ReducedEquiv, FiniteFourPlayerXORGame.reducedQuery] using
        (v4ReducedClause_spec hconflict c).1.symm
    have hb : InvolutionWord.ReducesToEmpty
        (word.map (fun c => v4Query ((v4ReducedEquiv hconflict |>.symm) c) p)) := by
      simpa [hq] using hbal p
    have hb' : InvolutionWord.ReducesToEmpty
        (wV.map (fun c => v4Query c p)) := by
      simpa [wV, List.map_map] using hb
    have hred1 : QIT.Research.FourXOR.Reducible
        (wV.map (fun c => v4Query c p)) := reducesToEmpty_reducible hb'
    have hproj : QIT.Research.FourXOR.projectionG wG α =
        (wV.map (fun c => v4Query c p)).map v4Bits := by
      simp [wG, QIT.Research.FourXOR.projectionG, QIT.Research.FourXOR.letterG,
        List.map_map, v4Query_eq_letter, hα]
    rw [hproj]
    exact reducible_map v4Bits hred1
  have hodd : Odd (QIT.Research.FourXOR.O0Count wG) := by
    have hsum : (word.map (fun c => v4Game.reducedSign hconflict c)).sum = 1 := by
      exact (parityPairing_occurrenceParity (v4Game.reducedSign hconflict) word).symm.trans hpar
    have hs : (wV.map v4Sign).sum = 1 := by
      have hm : word.map (fun c => v4Game.reducedSign hconflict c) =
          wV.map v4Sign := by
        dsimp [wV]
        rw [List.map_map]
        apply List.map_congr_left
        intro c hc
        have hpos : 0 < v4Game.weight
            (v4Query ((v4ReducedEquiv hconflict |>.symm) c),
              v4Sign ((v4ReducedEquiv hconflict |>.symm) c)) :=
          (v4Game_weight_pos_iff
            (v4Query ((v4ReducedEquiv hconflict |>.symm) c))
            (v4Sign ((v4ReducedEquiv hconflict |>.symm) c))).2
            ⟨(v4ReducedEquiv hconflict |>.symm) c, rfl, rfl⟩
        have hq' : v4Query ((v4ReducedEquiv hconflict |>.symm) c) = c.1 :=
          (v4ReducedClause_spec hconflict c).1
        have hpos' : 0 < v4Game.weight (c.1,
            v4Sign ((v4ReducedEquiv hconflict |>.symm) c)) := by
          simpa [hq'] using hpos
        exact (v4Game.reducedSign_unique hconflict c (b :=
          v4Sign ((v4ReducedEquiv hconflict |>.symm) c)) hpos').symm
      rw [← hm]
      exact hsum
    have hm' : wG.map (fun d : QIT.Research.FourXOR.GameClause (ZMod 2 × ZMod 2) =>
          if d.2 = true ∧ d.1 = 0 then (1 : ZMod 2) else 0) = wV.map v4Sign := by
      dsimp [wG]
      rw [List.map_map]
      apply List.map_congr_left
      intro c hc
      simp [v4Sign_eq_one_iff, v4Bits_eq_zero, v4Sign, and_comm]
    have hsum' : (wG.map (fun d => if d.2 = true ∧ d.1 = 0 then (1 : ZMod 2) else 0)).sum = 1 := by
      rw [hm']
      exact hs
    have hcnt : (((wG.map (fun d => if d.2 = true ∧ d.1 = 0 then (1 : ZMod 2) else 0)).count 1 : ℕ) : ZMod 2) = 1 := by
      have hz := zmod2_sum_eq_count_one
        (wG.map (fun d => if d.2 = true ∧ d.1 = 0 then (1 : ZMod 2) else 0))
      exact hz.symm.trans hsum'
    have hcnt2 : QIT.Research.FourXOR.O0Count wG =
        (wG.map (fun d => if d.2 = true ∧ d.1 = 0 then (1 : ZMod 2) else 0)).count 1 := by
      unfold QIT.Research.FourXOR.O0Count
      rw [countP_indicator_eq_count wG (fun c => c.2 = true ∧ c.1 = 0)]
    have hnat : ((QIT.Research.FourXOR.O0Count wG : ℕ) : ZMod 2) = 1 := by
      rw [hcnt2]
      exact hcnt
    have hmod : QIT.Research.FourXOR.O0Count wG % 2 = 1 := by
      have hcast := congrArg ZMod.val hnat
      simpa using hcast
    exact Nat.odd_iff.mpr hmod
  exact QIT.Research.FourXOR.klein_no_refutation wG ⟨hred, hodd⟩

theorem v4_value_one (hconflict : ¬ v4Game.HasConflictingTargets) :
    commutingOperatorValue v4Game = 1 := by
  rw [commutingOperatorValue_eq_one_iff_noOperatorRefutation v4Game hconflict]
  exact v4_no_operator_refutation hconflict

/-- The Klein four Cayley game witnesses sharp MERP separation at four
questions. -/
theorem v4_separation_at_most_4 : HasMERPSeparationAtMost 4 :=
  ⟨v4Game, ⟨v4_value_one v4_no_conflict, v4_no_MERP v4_no_conflict⟩⟩

/-- Four is the sharp MERP-separation threshold. -/
theorem four_is_sharp_threshold : IsSharpMERPSeparationThreshold 4 :=
  four_isSharpMERPSeparationThreshold_of_witness v4_separation_at_most_4

end

end XORGame
end QIT

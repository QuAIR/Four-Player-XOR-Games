/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.GameNormalization
public import XORGameFormalization.CommutingWord
public import XORGameFormalization.ObservableStrategy
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Data.Complex.Basic
public import Mathlib.Tactic

/-!
# General commuting-operator strategies

This module develops four-player commuting-operator strategies on arbitrary
complete complex inner-product spaces.  Perfectness is an eigenvector
condition on the shared state, not a global operator identity, and no finite
basis or matrix representation is assumed.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uQ uC uH uT uM

noncomputable section

open scoped ComplexConjugate

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]
variable {Hilbert : Type uH}

/-- The canonical complex inner product on `ULift`, pulled back from the base
space along `LinearIsometryEquiv.ulift`. -/
instance uliftInnerProductSpace (H : Type uH) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] : InnerProductSpace ℂ (ULift.{uT, uH} H) where
  toNormedSpace := inferInstance
  toInner := { inner := fun x y => inner ℂ x.1 y.1 }
  norm_sq_eq_re_inner := by
    intro x
    change ‖x.1‖ ^ 2 = (inner ℂ x.1 x.1).re
    exact InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) x.1
  conj_inner_symm := by
    intro x y
    change conj (inner ℂ y.1 x.1) = inner ℂ x.1 y.1
    exact InnerProductSpace.conj_inner_symm (𝕜 := ℂ) x.1 y.1
  add_left := by
    intro x y z
    change inner ℂ (x.1 + y.1) z.1 = inner ℂ x.1 z.1 + inner ℂ y.1 z.1
    exact InnerProductSpace.add_left (𝕜 := ℂ) x.1 y.1 z.1
  smul_left := by
    intro x y r
    change inner ℂ (r • x.1) y.1 = conj r * inner ℂ x.1 y.1
    exact InnerProductSpace.smul_left (𝕜 := ℂ) x.1 y.1 r

/--
A commuting-operator strategy on an arbitrary complete complex inner-product
space.
-/
structure FourPlayerCommutingOperatorStrategy
    (Question : Type uQ) (Hilbert : Type uH)
    [NormedAddCommGroup Hilbert]
    [InnerProductSpace ℂ Hilbert]
    [CompleteSpace Hilbert] where
  /-- The normalized shared state. -/
  state : Hilbert
  /-- The state has norm one. -/
  state_norm : ‖state‖ = 1
  /-- The observable used by a player on a question. -/
  observable : Fin 4 → Question → Hilbert →L[ℂ] Hilbert
  /-- Every observable is self-adjoint. -/
  isSelfAdjoint : ∀ player question, IsSelfAdjoint (observable player question)
  /-- Every observable is an involution. -/
  involutive : ∀ player question,
    observable player question * observable player question = 1
  /-- Observables of distinct players commute. -/
  cross_commute : ∀ {player player' : Fin 4}, player ≠ player' →
    ∀ question question',
      Commute (observable player question) (observable player' question')

namespace FourPlayerCommutingOperatorStrategy

variable {Hilbert : Type uH}
variable {ClauseId : Type uC}
variable [NormedAddCommGroup Hilbert] [InnerProductSpace ℂ Hilbert]
  [CompleteSpace Hilbert]

/-- The scalar binary phase as a continuous linear endomorphism. -/
def binaryContinuousPhase (sign : ZMod 2) : Hilbert →L[ℂ] Hilbert :=
  algebraMap ℂ (Hilbert →L[ℂ] Hilbert) (binaryXORPhase sign)

/-- The scalar phase is a monoid homomorphism from `ZMod 2`. -/
def binaryContinuousPhaseMonoid :
    Multiplicative (ZMod 2) →* Hilbert →L[ℂ] Hilbert :=
  (algebraMap ℂ (Hilbert →L[ℂ] Hilbert)).toMonoidHom.comp
    binaryXORPhase.toMonoidHom

@[simp]
theorem binaryContinuousPhase_apply (sign : ZMod 2) (x : Hilbert) :
    binaryContinuousPhase sign x = binaryXORPhase sign • x := by
  simp [binaryContinuousPhase]

/-- A nonzero normalized state cannot equal its own negation. -/
theorem state_ne_neg_self
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    strategy.state ≠ - strategy.state := by
  intro h
  have hsum : strategy.state + strategy.state = 0 := by
    exact add_eq_zero_iff_eq_neg.mpr h
  have htwo : (2 : ℂ) • strategy.state = 0 := by
    simpa [two_smul] using hsum
  have hzero : strategy.state = 0 := by
    exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hnorm : ‖strategy.state‖ = 0 := by
    rw [hzero]
    simp
  rw [strategy.state_norm] at hnorm
  norm_num at hnorm

/-- The scalar `-1` phase is not the identity operator. -/
theorem binaryContinuousPhase_one_ne_one
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    binaryContinuousPhaseMonoid (Multiplicative.ofAdd (1 : ZMod 2)) ≠
      (1 : Hilbert →L[ℂ] Hilbert) := by
  intro h
  have happ := (ContinuousLinearMap.ext_iff.mp h) strategy.state
  simp [binaryContinuousPhaseMonoid] at happ
  exact state_ne_neg_self strategy (by simpa using happ.symm)

/-- Conjugation of an endomorphism by the canonical `ULift` isometry. -/
def uliftOperator (A : Hilbert →L[ℂ] Hilbert) :
    ULift.{uT, uH} Hilbert →L[ℂ] ULift.{uT, uH} Hilbert :=
  (LinearIsometryEquiv.ulift ℂ Hilbert).symm ∘L A ∘L
    (LinearIsometryEquiv.ulift ℂ Hilbert)

private theorem uliftOperator_mul (A B : Hilbert →L[ℂ] Hilbert) :
    uliftOperator A * uliftOperator B = uliftOperator (A * B) := by
  ext x
  simp [uliftOperator]

/-- Transport a commuting-operator strategy along the canonical `ULift`
isometry into the target universe. -/
def uliftStrategy (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    FourPlayerCommutingOperatorStrategy Question (ULift.{uT, uH} Hilbert) where
  state := (LinearIsometryEquiv.ulift ℂ Hilbert).symm strategy.state
  state_norm := by
    rw [(LinearIsometryEquiv.ulift ℂ Hilbert).symm.norm_map]
    exact strategy.state_norm
  observable := fun p q => uliftOperator (strategy.observable p q)
  isSelfAdjoint := by
    intro p q
    have hA : ContinuousLinearMap.adjoint (strategy.observable p q) =
        strategy.observable p q := by
      simpa [IsSelfAdjoint] using strategy.isSelfAdjoint p q
    unfold IsSelfAdjoint
    change ContinuousLinearMap.adjoint (uliftOperator (strategy.observable p q)) =
      uliftOperator (strategy.observable p q)
    rw [show uliftOperator (strategy.observable p q) =
        (LinearIsometryEquiv.ulift ℂ Hilbert).symm ∘L (strategy.observable p q) ∘L
          (LinearIsometryEquiv.ulift ℂ Hilbert) by rfl]
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp]
    rw [LinearIsometryEquiv.adjoint_eq_symm, LinearIsometryEquiv.adjoint_eq_symm]
    rw [hA]
    simp [ContinuousLinearMap.comp_assoc]
  involutive := by
    intro p q
    ext x
    simp [uliftOperator]
    have hx : (strategy.observable p q) ((strategy.observable p q)
        ((LinearIsometryEquiv.ulift ℂ Hilbert) x)) =
        (LinearIsometryEquiv.ulift ℂ Hilbert) x := by
      change ((strategy.observable p q) * (strategy.observable p q))
        ((LinearIsometryEquiv.ulift ℂ Hilbert) x) =
        (LinearIsometryEquiv.ulift ℂ Hilbert) x
      rw [strategy.involutive p q]
      simp
    rw [hx]
    simp
  cross_commute := by
    intro p p' hne q q'
    unfold Commute
    ext x
    simp [uliftOperator]
    have hx := DFunLike.congr_fun (strategy.cross_commute hne q q').eq
      ((LinearIsometryEquiv.ulift ℂ Hilbert) x)
    simpa [hx]

/-- Evaluate one player's local involution word as a continuous operator. -/
def localObservableWordEval
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (player : Fin 4) :
    FreeMonoid Question →* Hilbert →L[ℂ] Hilbert :=
  FreeMonoid.lift (strategy.observable player)

@[simp]
theorem localObservableWordEval_singleton
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (player : Fin 4) (q : Question) :
    localObservableWordEval strategy player [q] = strategy.observable player q := by
  rw [localObservableWordEval, FreeMonoid.lift_apply]
  change (List.map (strategy.observable player) ([q] : List Question)).prod =
    strategy.observable player q
  simp

theorem localObservableWordEval_commute
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    {player player' : Fin 4} (hne : player ≠ player')
    (word word' : FreeMonoid Question) :
    Commute
      (localObservableWordEval strategy player word)
      (localObservableWordEval strategy player' word') := by
  rw [localObservableWordEval, FreeMonoid.lift_apply,
    localObservableWordEval, FreeMonoid.lift_apply]
  apply Commute.list_prod_left
  intro matrix hmatrix
  rw [List.mem_map] at hmatrix
  rcases hmatrix with ⟨question, _, rfl⟩
  apply Commute.list_prod_right
  intro matrix' hmatrix'
  rw [List.mem_map] at hmatrix'
  rcases hmatrix' with ⟨question', _, rfl⟩
  exact strategy.cross_commute hne question question'

private theorem list_product_eq_one_of_reduces
    {Letter : Type uQ} {M : Type uH} [Monoid M]
    (value : Letter → M)
    (hinvolutive : ∀ letter, value letter * value letter = 1)
    {word : List Letter}
    (hword : InvolutionWord.ReducesToEmpty word) :
    (word.map value).prod = 1 := by
  induction hword with
  | nil =>
      rfl
  | insert left right letter reduced ih =>
      rw [List.map_append, List.prod_append] at ih ⊢
      simp only [List.map_cons, List.prod_cons]
      calc
        (left.map value).prod *
            (value letter * (value letter * (right.map value).prod)) =
            (left.map value).prod *
              ((value letter * value letter) * (right.map value).prod) := by
                rw [mul_assoc]
        _ = (left.map value).prod * (right.map value).prod := by
              rw [hinvolutive]
              simp
        _ = 1 := ih

/-- A locally reducible word evaluates to the identity operator. -/
theorem localContinuousObservableWordEval_eq_one_of_reduces
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (player : Fin 4) (word : FreeMonoid Question)
    (hword :
      InvolutionWord.ReducesToEmpty (FreeMonoid.toList word)) :
    localObservableWordEval strategy player word = 1 := by
  rw [localObservableWordEval, FreeMonoid.lift_apply]
  exact list_product_eq_one_of_reduces
    (strategy.observable player) (strategy.involutive player) hword

/-- The fixed page order used by the concrete four-player evaluator. -/
def fourPlayerOrder : List (Fin 4) :=
  [0, 1, 2, 3]

/-- Every player occurs at most once in `fourPlayerOrder`. -/
theorem fourPlayerOrder_nodup :
    fourPlayerOrder.Nodup := by
  decide

/--
Evaluate a four-page word profile as a continuous operator product.
-/
def observableProfileEval
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) :
    (Fin 4 → FreeMonoid Question) →* Hilbert →L[ℂ] Hilbert where
  toFun profile :=
    (fourPlayerOrder.map fun player =>
      localObservableWordEval strategy player (profile player)).prod
  map_one' := by
    simp [fourPlayerOrder]
  map_mul' profile profile' := by
    change
      (fourPlayerOrder.map fun player =>
        localObservableWordEval strategy player
          (profile player * profile' player)).prod =
        (fourPlayerOrder.map fun player =>
          localObservableWordEval strategy player (profile player)).prod *
        (fourPlayerOrder.map fun player =>
          localObservableWordEval strategy player (profile' player)).prod
    simp only [map_mul]
    apply List.prod_map_mul_eq_mul_prod_map_of_cross
      fourPlayerOrder fourPlayerOrder_nodup
    intro player _ player' _ hne
    exact localObservableWordEval_commute strategy hne _ _

/-- A profile whose local words all reduce to the identity evaluates to the
identity operator. -/
theorem observableProfileEval_reduced_eq_one
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (profile : Fin 4 → FreeMonoid Question)
    (hreduced :
      ∀ player,
        InvolutionWord.ReducesToEmpty
          (FreeMonoid.toList (profile player))) :
    observableProfileEval strategy profile = 1 := by
  change
    (fourPlayerOrder.map fun player =>
      localObservableWordEval strategy player (profile player)).prod = 1
  apply List.prod_eq_one
  intro matrix hmatrix
  rw [List.mem_map] at hmatrix
  rcases hmatrix with ⟨player, _, rfl⟩
  exact localContinuousObservableWordEval_eq_one_of_reduces
    strategy player (profile player) (hreduced player)

/-- A balanced clause word evaluates to the identity operator. -/
theorem balancedWord_operatorProduct_eq_identity
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId)
    (hbalanced : IsBalancedWord query word) :
    observableProfileEval strategy (wordProfile query word) = 1 :=
  observableProfileEval_reduced_eq_one strategy _ fun player => by
    rw [wordProfile_apply]
    exact hbalanced player

/-- The ordered product of the four observables in a clause. -/
def clauseOperator
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    Hilbert →L[ℂ] Hilbert :=
  strategy.observable 0 (query 0) *
  strategy.observable 1 (query 1) *
  strategy.observable 2 (query 2) *
  strategy.observable 3 (query 3)

/-- A permutation of a list whose elements pairwise commute has the same
product as the original list. -/
private theorem perm_pairwise_of_symm {α : Type uM} {R : α → α → Prop}
    (hR : Symmetric R) {l₁ l₂ : List α} (h : l₁.Perm l₂)
    (hp : l₁.Pairwise R) : l₂.Pairwise R := by
  induction h with
  | nil => simpa using hp
  | cons a h ih =>
      match hp with
      | .cons hhead htail =>
          constructor
          · intro b hb
            exact hhead b (h.mem_iff.mpr hb)
          · exact ih htail
  | swap a b l =>
      match hp with
      | .cons hhead htail =>
          match htail with
          | .cons hheadA htailA =>
              constructor
              · intro c hc
                rcases (List.mem_cons.mp hc) with hcb | hc
                · subst hcb
                  exact hR (hhead a (by simp))
                · exact hheadA c hc
              · constructor
                · intro c hc
                  exact hhead c (by simpa [List.mem_cons] using Or.inr hc)
                · exact htailA
  | trans h₁ h₂ ih₁ ih₂ =>
      exact ih₂ (ih₁ hp)

private theorem perm_prod_eq_of_pairwise_commute {M : Type uM} [Monoid M]
    {l₁ l₂ : List M} (h : l₁.Perm l₂)
    (hcomm : l₁.Pairwise (fun a b => Commute a b)) :
    l₁.prod = l₂.prod := by
  induction h with
  | nil => rfl
  | cons a h ih =>
      match hcomm with
      | .cons hhead htail =>
          rw [List.prod_cons, List.prod_cons, ih htail]
  | swap a b l =>
      match hcomm with
      | .cons hhead htail =>
          match htail with
          | .cons hhead' htail' =>
              have hab : Commute b a := hhead a (by simp)
              calc
                (b :: a :: l).prod = b * (a * l.prod) := rfl
                _ = (b * a) * l.prod := by rw [mul_assoc]
                _ = (a * b) * l.prod := by rw [hab]
                _ = a * (b * l.prod) := by rw [← mul_assoc]
                _ = (a :: b :: l).prod := rfl
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ hcomm).trans
        (ih₂ (perm_pairwise_of_symm (by intro a b h; exact h.symm) h₁ hcomm))

/-- The observables on the four players pairwise commute. -/
private theorem clauseObservablePairwise
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    ((List.finRange 4).map (fun q => strategy.observable q (query q))).Pairwise
      (fun a b => Commute a b) := by
  norm_num [List.finRange]
  constructor
  · constructor
    · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 1) _ _
    · constructor
      · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 2) _ _
      · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 3) _ _
  · constructor
    · constructor
      · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 2) _ _
      · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 3) _ _
    · exact strategy.cross_commute (by decide : (2 : Fin 4) ≠ 3) _ _

/-- Swapping the questions of two distinct players does not change the
ordered clause operator, because observables of distinct players commute. -/
theorem clauseOperator_commute_reorder
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) {p p' : Fin 4} (hne : p ≠ p') :
    ((List.finRange 4).map (fun r =>
        strategy.observable (Equiv.swap p p' r) (query (Equiv.swap p p' r)))).prod =
      strategy.clauseOperator query := by
  have hprod : ∀ q : FourPlayerQuestionTuple Question,
      strategy.clauseOperator q =
        ((List.finRange 4).map (fun r => strategy.observable r (q r))).prod := by
    intro q
    simp [clauseOperator, List.finRange, mul_assoc]
  rw [hprod]
  let obs : Fin 4 → Hilbert →L[ℂ] Hilbert := fun q => strategy.observable q (query q)
  change ((List.finRange 4).map (fun r => obs (Equiv.swap p p' r))).prod =
    ((List.finRange 4).map obs).prod
  have hperm : ((List.finRange 4).map (fun r => obs (Equiv.swap p p' r))).Perm
      ((List.finRange 4).map obs) := by
    change (List.map (obs ∘ Equiv.swap p p') (List.finRange 4)).Perm
      ((List.finRange 4).map obs)
    rw [← List.map_map]
    exact (Equiv.Perm.map_finRange_perm (Equiv.swap p p')).map obs
  have hpair : ((List.finRange 4).map (fun r => obs (Equiv.swap p p' r))).Pairwise
      (fun a b => Commute a b) := by
    exact perm_pairwise_of_symm (by intro a b h; exact h.symm) hperm.symm
      (clauseObservablePairwise strategy query)
  exact perm_prod_eq_of_pairwise_commute hperm hpair

/-- A compile example exercising the reorder theorem with a nontrivial
permutation of two distinct players. -/
example (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    ((List.finRange 4).map (fun r =>
        strategy.observable (Equiv.swap (0 : Fin 4) 2 r) (query (Equiv.swap 0 2 r)))).prod =
      strategy.clauseOperator query :=
  clauseOperator_commute_reorder strategy query (by decide : (0 : Fin 4) ≠ 2)

/-- The clause operator of the lifted strategy is the lifted clause operator. -/
theorem uliftStrategy_clauseOperator
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    (uliftStrategy strategy).clauseOperator query = uliftOperator (strategy.clauseOperator query) := by
  simp [clauseOperator, uliftStrategy, uliftOperator_mul, mul_assoc]

/-- The lifted clause operator acts componentwise. -/
theorem uliftStrategy_clauseOperator_apply
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) (x : ULift.{uT, uH} Hilbert) :
    (uliftStrategy strategy).clauseOperator query x = ULift.up (strategy.clauseOperator query x.1) := by
  rw [uliftStrategy_clauseOperator]
  rfl

theorem observableProfileEval_clauseWordProfile_eq_clauseOperator
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (c : ClauseId) :
    observableProfileEval strategy (clauseWordProfile query c) =
      strategy.clauseOperator (query c) := by
  simp [observableProfileEval, clauseWordProfile, clauseOperator, fourPlayerOrder,
    localObservableWordEval_singleton, mul_assoc]

/-- The word product of clause operators equals the observable-profile
evaluation of the corresponding clause word. -/
theorem word_operatorProduct_eq_observableProfileEval
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId) :
    (word.map (fun c => strategy.clauseOperator (query c))).prod =
      observableProfileEval strategy (wordProfile query word) := by
  induction word with
  | nil => simp [wordProfile]
  | cons c tail ih =>
      rw [List.map_cons, List.prod_cons]
      rw [wordProfile]
      simp only [List.map_cons, List.prod_cons]
      rw [(observableProfileEval strategy).map_mul _ _]
      change strategy.clauseOperator (query c) *
          (List.map (fun c => strategy.clauseOperator (query c)) tail).prod =
        strategy.clauseOperator (query c) *
          observableProfileEval strategy (wordProfile query tail)
      rw [← ih]

private theorem observable0_commute_rest
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    Commute (strategy.observable 0 (query 0))
      (strategy.observable 1 (query 1) * strategy.observable 2 (query 2) *
        strategy.observable 3 (query 3)) := by
  apply Commute.mul_right
  · apply Commute.mul_right
    · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 1) _ _
    · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 2) _ _
  · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 3) _ _

private theorem observable01_commute_rest
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    Commute (strategy.observable 0 (query 0) * strategy.observable 1 (query 1))
      (strategy.observable 2 (query 2) * strategy.observable 3 (query 3)) := by
  apply Commute.mul_right
  · apply Commute.mul_left
    · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 2) _ _
    · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 2) _ _
  · apply Commute.mul_left
    · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 3) _ _
    · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 3) _ _

/-- The ordered clause operator is self-adjoint. -/
theorem clauseOperator_isSelfAdjoint
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    IsSelfAdjoint (strategy.clauseOperator query) := by
  have h0 : IsSelfAdjoint (strategy.observable 0 (query 0)) :=
    strategy.isSelfAdjoint 0 (query 0)
  have h1 : IsSelfAdjoint (strategy.observable 1 (query 1)) :=
    strategy.isSelfAdjoint 1 (query 1)
  have h2 : IsSelfAdjoint (strategy.observable 2 (query 2)) :=
    strategy.isSelfAdjoint 2 (query 2)
  have h3 : IsSelfAdjoint (strategy.observable 3 (query 3)) :=
    strategy.isSelfAdjoint 3 (query 3)
  have h01 : IsSelfAdjoint (strategy.observable 0 (query 0) *
      strategy.observable 1 (query 1)) :=
    (IsSelfAdjoint.commute_iff h0 h1).mp
      (strategy.cross_commute (by decide : (0 : Fin 4) ≠ 1) _ _)
  have h012 : IsSelfAdjoint
      ((strategy.observable 0 (query 0) * strategy.observable 1 (query 1)) *
        strategy.observable 2 (query 2)) :=
    (IsSelfAdjoint.commute_iff h01 h2).mp (by
      apply Commute.mul_left
      · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 2) _ _
      · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 2) _ _)
  have h0123 : IsSelfAdjoint
      (((strategy.observable 0 (query 0) * strategy.observable 1 (query 1)) *
          strategy.observable 2 (query 2)) * strategy.observable 3 (query 3)) :=
    (IsSelfAdjoint.commute_iff h012 h3).mp (by
      apply Commute.mul_left
      · apply Commute.mul_left
        · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 3) _ _
        · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 3) _ _
      · exact strategy.cross_commute (by decide : (2 : Fin 4) ≠ 3) _ _)
  simpa [clauseOperator] using h0123

/-- The ordered clause operator is an involution. -/
theorem clauseOperator_involutive
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    strategy.clauseOperator query * strategy.clauseOperator query = 1 := by
  let A0 := strategy.observable 0 (query 0)
  let A1 := strategy.observable 1 (query 1)
  let A2 := strategy.observable 2 (query 2)
  let A3 := strategy.observable 3 (query 3)
  have h01 : Commute A0 A1 := strategy.cross_commute (by decide : (0 : Fin 4) ≠ 1) _ _
  have h23 : Commute A2 A3 := strategy.cross_commute (by decide : (2 : Fin 4) ≠ 3) _ _
  have hXY : Commute (A0 * A1) (A2 * A3) := by
    apply Commute.mul_right
    · apply Commute.mul_left
      · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 2) _ _
      · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 2) _ _
    · apply Commute.mul_left
      · exact strategy.cross_commute (by decide : (0 : Fin 4) ≠ 3) _ _
      · exact strategy.cross_commute (by decide : (1 : Fin 4) ≠ 3) _ _
  have hpair01 : (A0 * A1) * (A0 * A1) = 1 := by
    calc
      (A0 * A1) * (A0 * A1) = A0 * (A1 * A0) * A1 := by simp [mul_assoc]
      _ = A0 * (A0 * A1) * A1 := by rw [h01.eq]
      _ = (A0 * A0) * (A1 * A1) := by simp [mul_assoc]
      _ = 1 := by simp [A0, A1, strategy.involutive 0 (query 0), strategy.involutive 1 (query 1)]
  have hpair23 : (A2 * A3) * (A2 * A3) = 1 := by
    calc
      (A2 * A3) * (A2 * A3) = A2 * (A3 * A2) * A3 := by simp [mul_assoc]
      _ = A2 * (A2 * A3) * A3 := by rw [h23.eq]
      _ = (A2 * A2) * (A3 * A3) := by simp [mul_assoc]
      _ = 1 := by simp [A2, A3, strategy.involutive 2 (query 2), strategy.involutive 3 (query 3)]
  calc
    strategy.clauseOperator query * strategy.clauseOperator query =
        ((A0 * A1) * (A2 * A3)) * ((A0 * A1) * (A2 * A3)) := by
          simp [clauseOperator, A0, A1, A2, A3, mul_assoc]
    _ = ((A0 * A1) * (A0 * A1)) * ((A2 * A3) * (A2 * A3)) := by
          calc
            ((A0 * A1) * (A2 * A3)) * ((A0 * A1) * (A2 * A3)) =
                (A0 * A1) * ((A2 * A3) * (A0 * A1)) * (A2 * A3) := by simp [mul_assoc]
            _ = (A0 * A1) * ((A0 * A1) * (A2 * A3)) * (A2 * A3) := by rw [hXY.eq]
            _ = ((A0 * A1) * (A0 * A1)) * ((A2 * A3) * (A2 * A3)) := by simp [mul_assoc]
    _ = 1 := by rw [hpair01, hpair23]; simp

/-- The ordered clause operator for an indexed clause. -/
def clauseObservable
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (clause : ClauseId) :
    Hilbert →L[ℂ] Hilbert :=
  strategy.clauseOperator (query clause)

/-- Exact signed-clause satisfaction by state action. -/
def SatisfiesSignedClause
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) (sign : ZMod 2) : Prop :=
  strategy.clauseOperator query strategy.state =
    binaryXORPhase sign • strategy.state

/-- Lifting preserves signed-clause satisfaction. -/
theorem uliftStrategy_satisfiesSignedClause_iff
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) (sign : ZMod 2) :
    ((uliftStrategy strategy : FourPlayerCommutingOperatorStrategy Question
        (ULift.{uT, uH} Hilbert)).SatisfiesSignedClause query sign) ↔
      strategy.SatisfiesSignedClause query sign := by
  unfold SatisfiesSignedClause
  constructor
  · intro h
    have he := congrArg (fun z : ULift.{uT, uH} Hilbert =>
        (LinearIsometryEquiv.ulift ℂ Hilbert) z) h
    simpa [uliftStrategy_clauseOperator_apply, map_smul] using he
  · intro h
    have he := congrArg (fun z : Hilbert =>
        (LinearIsometryEquiv.ulift ℂ Hilbert).symm z) h
    simpa [uliftStrategy_clauseOperator_apply, map_smul] using he

/-- A strategy is perfect when every indexed signed clause is satisfied. -/
def IsPerfectCommutingOperatorStrategy
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) : Prop :=
  ∀ clause : ClauseId,
    strategy.SatisfiesSignedClause (query clause) (sign clause)

/-- A strategy is perfect on the raw positive support of a game. -/
def IsPerfectCommutingOperatorStrategyOnSupport
    (G : FiniteFourPlayerXORGame Question)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert) : Prop :=
  ∀ clause : SignedFourPlayerClause Question,
    clause ∈ G.support → strategy.SatisfiesSignedClause clause.1 clause.2

/-- A bundled model of a perfect commuting-operator strategy. -/
structure PerfectCommutingOperatorModel
    (G : FiniteFourPlayerXORGame Question) where
  Hilbert : Type (max uQ 0)
  [normedAddCommGroup : NormedAddCommGroup Hilbert]
  [innerProductSpace : InnerProductSpace ℂ Hilbert]
  [completeSpace : CompleteSpace Hilbert]
  strategy : FourPlayerCommutingOperatorStrategy Question Hilbert
  perfect : IsPerfectCommutingOperatorStrategyOnSupport G strategy

/-- A game has a perfect commuting-operator strategy when such a bundled
model exists in the fixed game-group universe. -/
def HasPerfectCommutingOperatorStrategy
    (G : FiniteFourPlayerXORGame Question) : Prop :=
  Nonempty (PerfectCommutingOperatorModel G)

/-- A word of clause operators in a perfect strategy acts on the state by the
product of the binary clause phases. -/
theorem perfectWord_operatorProduct_apply
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (hperfect : IsPerfectCommutingOperatorStrategy query sign strategy)
    (word : List ClauseId) :
    observableProfileEval strategy (wordProfile query word) strategy.state =
      binaryXORPhase ((word.map sign).sum) • strategy.state := by
  induction word with
  | nil =>
      simp [wordProfile]
  | cons clause tail ih =>
      calc
        observableProfileEval strategy
              (wordProfile query (clause :: tail)) strategy.state =
            (clauseObservable strategy query clause *
                observableProfileEval strategy (wordProfile query tail))
              strategy.state := by
                congr 1
                change
                  observableProfileEval strategy
                      (clauseWordProfile query clause *
                        wordProfile query tail) =
                    observableProfileEval strategy
                        (clauseWordProfile query clause) *
                      observableProfileEval strategy
                        (wordProfile query tail)
                exact (observableProfileEval strategy).map_mul _ _
        _ = clauseObservable strategy query clause
              (observableProfileEval strategy (wordProfile query tail)
                strategy.state) := by
                rfl
        _ = clauseObservable strategy query clause
              (binaryXORPhase ((tail.map sign).sum) •
                strategy.state) := by
                rw [ih]
        _ = binaryXORPhase ((tail.map sign).sum) •
              (clauseObservable strategy query clause strategy.state) := by
                simp
        _ = binaryXORPhase ((tail.map sign).sum) •
              (binaryXORPhase (sign clause) • strategy.state) := by
                change binaryXORPhase ((tail.map sign).sum) •
                    (strategy.clauseOperator (query clause) strategy.state) =
                  binaryXORPhase ((tail.map sign).sum) •
                    (binaryXORPhase (sign clause) • strategy.state)
                rw [hperfect clause]
        _ = binaryXORPhase ((clause :: tail).map sign).sum •
              strategy.state := by
                simp only [List.map_cons, List.sum_cons, binaryXORPhase_add,
                  smul_smul]
                rw [mul_comm]

/-- The word of an operator refutation acts by `-1` on the state of any
putative perfect strategy. -/
theorem operatorRefutationWord_operatorProduct_apply_eq_neg
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (word : List ClauseId)
    (hrefutation : IsOperatorRefutation query sign word)
    (hperfect : IsPerfectCommutingOperatorStrategy query sign strategy) :
    observableProfileEval strategy (wordProfile query word) strategy.state =
      - strategy.state := by
  have hsignSum : (word.map sign).sum = 1 := by
    rw [← parityPairing_occurrenceParity]
    exact hrefutation.2
  rw [perfectWord_operatorProduct_apply query sign strategy hperfect word,
    hsignSum]
  simp [binaryXORPhase_one]

/-- An operator refutation excludes every exact perfect commuting-operator
strategy. -/
theorem operatorRefutation_excludes_perfectCommutingOperatorStrategy
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (hrefutation : HasOperatorRefutation query sign) :
    ¬ IsPerfectCommutingOperatorStrategy query sign strategy := by
  rintro hperfect
  rcases hrefutation with ⟨word, hword⟩
  have hevalOne :
      observableProfileEval strategy (wordProfile query word) = 1 :=
    balancedWord_operatorProduct_eq_identity query strategy word hword.1
  have haction :=
    operatorRefutationWord_operatorProduct_apply_eq_neg
      query sign strategy word hword hperfect
  rw [hevalOne] at haction
  exact state_ne_neg_self strategy (by simpa using haction)

/-- A strategy cannot satisfy both target signs of one query. -/
theorem not_satisfies_both
    (strategy : FourPlayerCommutingOperatorStrategy Question Hilbert)
    (query : FourPlayerQuestionTuple Question) :
    ¬ (strategy.SatisfiesSignedClause query (0 : ZMod 2) ∧
      strategy.SatisfiesSignedClause query (1 : ZMod 2)) := by
  rintro ⟨hzero, hone⟩
  have hzero' : strategy.clauseOperator query strategy.state = strategy.state := by
    simpa [SatisfiesSignedClause] using hzero
  have hone' : strategy.clauseOperator query strategy.state =
      - strategy.state := by
    simpa [SatisfiesSignedClause, binaryXORPhase_one] using hone
  have hneg : strategy.state = - strategy.state := by
    calc
      strategy.state = strategy.clauseOperator query strategy.state := hzero'.symm
      _ = - strategy.state := hone'
  exact state_ne_neg_self strategy hneg

/-- A target conflict excludes every perfect commuting-operator strategy. -/
theorem conflictingTargets_exclude_perfectCommutingOperatorStrategy
    (G : FiniteFourPlayerXORGame Question) :
    G.HasConflictingTargets → ¬ HasPerfectCommutingOperatorStrategy G := by
  rintro hconflict ⟨model⟩
  letI := model.normedAddCommGroup
  letI := model.innerProductSpace
  letI := model.completeSpace
  exact
    FiniteFourPlayerXORGame.conflictingTargets_exclude_deterministic_clause_satisfaction
      G (fun clause => model.strategy.SatisfiesSignedClause clause.1 clause.2)
      hconflict
      (fun query hboth => not_satisfies_both model.strategy query hboth)
      model.perfect

end FourPlayerCommutingOperatorStrategy

end

end XORGame
end QIT

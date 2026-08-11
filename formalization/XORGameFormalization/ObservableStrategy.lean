/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.Pure
public import XORGameFormalization.CommutingWord
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar

/-!
# Four-player binary XOR strategies from commuting observables

This module connects the algebraic operator-refutation layer to concrete
finite-dimensional commuting-observable strategies.  A strategy consists of a
normalized pure state and one Hermitian involution for every player/question.
Observables belonging to different players commute.

Perfect play is expressed by the exact clause eigenvector equations on the
state.  These equations are weaker, and physically more appropriate, than
requiring every clause product to equal its sign as a matrix on the whole
Hilbert space.  The main theorem nevertheless shows that an operator
refutation excludes such a perfect strategy: balance makes the refutation
product the identity matrix, while the clause eigenvector equations make the
same product act by the odd binary phase.
-/

@[expose] public section

open Matrix

namespace QIT
namespace XORGame

universe uQ uC uH uI uM

noncomputable section

variable {Question : Type uQ} {ClauseId : Type uC} {Hilbert : Type uH}

/--
A finite-dimensional four-player binary-observable strategy.

`involutive` says that every observable has outcomes in `±1`.
`cross_commute` is imposed only between distinct players; observables for
different questions of the same player need not commute.
-/
structure FourPlayerBinaryObservableStrategy
    (Question : Type uQ) (Hilbert : Type uH)
    [Fintype Hilbert] [DecidableEq Hilbert] where
  /-- The normalized shared pure state. -/
  state : PureVector Hilbert
  /-- The observable used by a player on a question. -/
  observable : Fin 4 → Question → CMatrix Hilbert
  /-- Binary observables are Hermitian. -/
  isHermitian :
    ∀ player question, (observable player question).IsHermitian
  /-- Binary observables square to the identity. -/
  involutive :
    ∀ player question, observable player question * observable player question = 1
  /-- Observables of distinct players commute. -/
  cross_commute :
    ∀ {player player' : Fin 4}, player ≠ player' →
      ∀ question question',
        Commute (observable player question) (observable player' question')

/-- A trace-normalized pure vector is nonzero. -/
theorem pureVector_amp_ne_zero
    [Fintype Hilbert] [DecidableEq Hilbert]
    (state : PureVector Hilbert) :
    state.amp ≠ 0 := by
  intro hzero
  have htrace := state.trace_rankOne_eq_one
  rw [hzero] at htrace
  simp [rankOneMatrix] at htrace

/-- The canonical binary phase character, with values `+1` and `-1`. -/
def binaryXORPhase : AddChar (ZMod 2) ℂ :=
  ZMod.stdAddChar

@[simp]
theorem binaryXORPhase_zero :
    binaryXORPhase 0 = 1 :=
  AddChar.map_zero_eq_one _

theorem binaryXORPhase_add (a b : ZMod 2) :
    binaryXORPhase (a + b) = binaryXORPhase a * binaryXORPhase b :=
  AddChar.map_add_eq_mul _ _ _

theorem binaryXORPhase_one_ne_one :
    binaryXORPhase 1 ≠ 1 := by
  intro h
  have hzero : binaryXORPhase (0 : ZMod 2) = 1 :=
    binaryXORPhase_zero
  have : (1 : ZMod 2) = 0 :=
    ZMod.injective_stdAddChar (h.trans hzero.symm)
  exact one_ne_zero this

@[simp]
theorem binaryXORPhase_one :
    binaryXORPhase 1 = -1 := by
  apply (mul_self_eq_one_iff.mp ?_).resolve_left binaryXORPhase_one_ne_one
  rw [← binaryXORPhase_add]
  have htwo : (1 : ZMod 2) + 1 = 0 := by
    decide
  rw [htwo]
  exact binaryXORPhase_zero

/-- Evaluate one player's local involution word as a matrix product. -/
def localObservableWordEval
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (player : Fin 4) :
    FreeMonoid Question →* CMatrix Hilbert :=
  FreeMonoid.lift (strategy.observable player)

theorem localObservableWordEval_commute
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
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
    {Letter : Type uQ} {M : Type uM} [Monoid M]
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

theorem localObservableWordEval_eq_one_of_reduces
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
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
Transpose two layers of a noncommutative list product when a right factor at
an earlier, distinct index commutes with every later left factor.
-/
theorem List.prod_map_mul_eq_mul_prod_map_of_cross
    {Index : Type uI} {M : Type uM} [Monoid M]
    (indices : List Index) (hindices : indices.Nodup)
    (left right : Index → M)
    (hcross :
      ∀ i ∈ indices, ∀ j ∈ indices, i ≠ j →
        Commute (right i) (left j)) :
    (indices.map fun i => left i * right i).prod =
      (indices.map left).prod * (indices.map right).prod := by
  induction indices with
  | nil =>
      simp
  | cons index tail ih =>
      rw [List.nodup_cons] at hindices
      simp only [List.map_cons, List.prod_cons]
      have ih' :
          (tail.map fun i => left i * right i).prod =
            (tail.map left).prod * (tail.map right).prod :=
        ih hindices.2 fun i hi j hj hne =>
          hcross i (by simp [hi]) j (by simp [hj]) hne
      rw [ih']
      have hcommute :
            Commute (right index) (tail.map left).prod := by
          apply Commute.list_prod_right
          intro value hvalue
          rw [List.mem_map] at hvalue
          rcases hvalue with ⟨index', hindex', rfl⟩
          have hne : index ≠ index' := by
            intro heq
            subst index'
            exact hindices.1 hindex'
          exact hcross index (by simp) index' (by simp [hindex'])
            hne
      calc
        (left index * right index) *
            ((tail.map left).prod * (tail.map right).prod) =
            left index *
              (right index *
                ((tail.map left).prod * (tail.map right).prod)) := by
                  rw [mul_assoc]
        _ = left index *
              ((tail.map left).prod *
                (right index * (tail.map right).prod)) := by
                  rw [hcommute.left_comm]
        _ = (left index * (tail.map left).prod) *
              (right index * (tail.map right).prod) := by
                  rw [mul_assoc]

/--
Evaluate a four-page word profile.  The fixed order is players `0,1,2,3`.
Cross-player commutation is exactly what makes this evaluator multiplicative.
-/
def observableProfileEval
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert) :
    (Fin 4 → FreeMonoid Question) →* CMatrix Hilbert where
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

theorem observableProfileEval_reduced_eq_one
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
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
  exact localObservableWordEval_eq_one_of_reduces
    strategy player (profile player) (hreduced player)

/--
A balanced clause word evaluates to the identity for every concrete
four-player commuting-observable strategy.
-/
theorem balancedWord_observableProfileEval_eq_one
    [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (word : List ClauseId)
    (hbalanced : IsBalancedWord query word) :
    observableProfileEval strategy (wordProfile query word) = 1 :=
  observableProfileEval_reduced_eq_one strategy _ fun player => by
    rw [wordProfile_apply]
    exact hbalanced player

/-- The binary scalar phase embedded as a scalar matrix. -/
def binaryXORMatrixPhase
    [Fintype Hilbert] [DecidableEq Hilbert] :
    Multiplicative (ZMod 2) →* CMatrix Hilbert :=
  (algebraMap ℂ (CMatrix Hilbert)).toMonoidHom.comp
    binaryXORPhase.toMonoidHom

@[simp]
theorem binaryXORMatrixPhase_apply
    [Fintype Hilbert] [DecidableEq Hilbert]
    (sign : ZMod 2) :
    binaryXORMatrixPhase (Hilbert := Hilbert)
        (Multiplicative.ofAdd sign) =
      algebraMap ℂ (CMatrix Hilbert) (binaryXORPhase sign) :=
  rfl

theorem binaryXORMatrixPhase_one_ne_one
    [Fintype Hilbert] [DecidableEq Hilbert]
    (state : PureVector Hilbert) :
    binaryXORMatrixPhase (Hilbert := Hilbert)
        (Multiplicative.ofAdd (1 : ZMod 2)) ≠
      (1 : CMatrix Hilbert) := by
  obtain ⟨index, _⟩ :=
    Function.ne_iff.mp (pureVector_amp_ne_zero state)
  intro h
  have hdiagonal := congrFun (congrFun h index) index
  norm_num [binaryXORMatrixPhase, binaryXORPhase_one] at hdiagonal

/--
Concrete commuting observables supply the evaluator and reduction fields of
`CommutingWordRealization`.  The phase is the scalar `ZMod 2` character.

This realization is an operator-level bridge only.  Perfectness of the
physical strategy below is deliberately a clause equation on `state.amp`, not
the stronger whole-matrix predicate `IsPerfectCommutingWordRealization`.
-/
def FourPlayerBinaryObservableStrategy.toCommutingWordRealization
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert) :
    CommutingWordRealization (Fin 4) Question (CMatrix Hilbert) where
  eval := observableProfileEval strategy
  phase := binaryXORMatrixPhase
  phase_one_ne_one :=
    binaryXORMatrixPhase_one_ne_one strategy.state
  reduced_eval_one :=
    observableProfileEval_reduced_eq_one strategy

@[simp]
theorem FourPlayerBinaryObservableStrategy.toCommutingWordRealization_eval
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (profile : Fin 4 → FreeMonoid Question) :
    strategy.toCommutingWordRealization.eval profile =
      observableProfileEval strategy profile :=
  rfl

/-- The ordered product of the four observables in a clause. -/
def clauseObservable
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (query : ClauseId → Clause (Fin 4) Question)
    (clause : ClauseId) :
    CMatrix Hilbert :=
  observableProfileEval strategy (clauseWordProfile query clause)

@[simp]
theorem clauseObservable_eq_four_product
    [Fintype Hilbert] [DecidableEq Hilbert]
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (query : ClauseId → Clause (Fin 4) Question)
    (clause : ClauseId) :
    clauseObservable strategy query clause =
      strategy.observable 0 (query clause 0) *
      strategy.observable 1 (query clause 1) *
      strategy.observable 2 (query clause 2) *
      strategy.observable 3 (query clause 3) := by
  change
    ([
      strategy.observable 0 (query clause 0),
      strategy.observable 1 (query clause 1),
      strategy.observable 2 (query clause 2),
      strategy.observable 3 (query clause 3)
    ] : List (CMatrix Hilbert)).prod =
      strategy.observable 0 (query clause 0) *
      strategy.observable 1 (query clause 1) *
      strategy.observable 2 (query clause 2) *
      strategy.observable 3 (query clause 3)
  simp [mul_assoc]

/--
Exact perfect play on the shared state: every signed clause product has the
state as an eigenvector with its binary XOR phase.
-/
def IsPerfectFourPlayerBinaryObservableStrategy
    [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert) : Prop :=
  ∀ clause,
    clauseObservable strategy query clause *ᵥ strategy.state.amp =
      binaryXORPhase (sign clause) • strategy.state.amp

/--
The product of any clause word in a perfect strategy acts on the shared state
by the product of its binary clause phases.
-/
theorem perfectWord_observableProfileEval_mulVec
    [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (hperfect :
      IsPerfectFourPlayerBinaryObservableStrategy query sign strategy)
    (word : List ClauseId) :
    observableProfileEval strategy (wordProfile query word) *ᵥ
        strategy.state.amp =
      binaryXORPhase ((word.map sign).sum) • strategy.state.amp := by
  induction word with
  | nil =>
      simp [wordProfile]
  | cons clause tail ih =>
      calc
        observableProfileEval strategy
              (wordProfile query (clause :: tail)) *ᵥ
            strategy.state.amp =
            (clauseObservable strategy query clause *
                observableProfileEval strategy (wordProfile query tail)) *ᵥ
              strategy.state.amp := by
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
        _ = clauseObservable strategy query clause *ᵥ
              (observableProfileEval strategy (wordProfile query tail) *ᵥ
                strategy.state.amp) := by
                rw [Matrix.mulVec_mulVec]
        _ = clauseObservable strategy query clause *ᵥ
              (binaryXORPhase ((tail.map sign).sum) •
                strategy.state.amp) := by
                rw [ih]
        _ = binaryXORPhase ((tail.map sign).sum) •
              (clauseObservable strategy query clause *ᵥ
                strategy.state.amp) := by
                rw [Matrix.mulVec_smul]
        _ = binaryXORPhase ((tail.map sign).sum) •
              (binaryXORPhase (sign clause) • strategy.state.amp) := by
                rw [hperfect clause]
        _ = binaryXORPhase ((clause :: tail).map sign).sum •
              strategy.state.amp := by
                simp only [List.map_cons, List.sum_cons, binaryXORPhase_add,
                  smul_smul]
                rw [mul_comm]

/--
The word of an operator refutation acts by `-1` on the state of any putative
perfect strategy.
-/
theorem operatorRefutationWord_observableProfileEval_mulVec_eq_neg
    [Fintype ClauseId] [DecidableEq ClauseId]
    [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (word : List ClauseId)
    (hrefutation : IsOperatorRefutation query sign word)
    (hperfect :
      IsPerfectFourPlayerBinaryObservableStrategy query sign strategy) :
    observableProfileEval strategy (wordProfile query word) *ᵥ
        strategy.state.amp =
      -strategy.state.amp := by
  have hsignSum : (word.map sign).sum = 1 := by
    rw [← parityPairing_occurrenceParity]
    exact hrefutation.2
  rw [perfectWord_observableProfileEval_mulVec
    query sign strategy hperfect word, hsignSum]
  simp

/--
An operator refutation excludes every finite-dimensional exact perfect
four-player commuting-observable strategy.
-/
theorem operatorRefutation_excludes_perfectFourPlayerBinaryObservableStrategy
    [Fintype ClauseId] [DecidableEq ClauseId]
    [Fintype Hilbert] [DecidableEq Hilbert]
    (query : ClauseId → Clause (Fin 4) Question)
    (sign : ClauseId → ZMod 2)
    (strategy : FourPlayerBinaryObservableStrategy Question Hilbert)
    (hrefutation : HasOperatorRefutation query sign) :
    ¬ IsPerfectFourPlayerBinaryObservableStrategy query sign strategy := by
  rintro hperfect
  rcases hrefutation with ⟨word, hword⟩
  have hevalOne :
      observableProfileEval strategy (wordProfile query word) = 1 :=
    balancedWord_observableProfileEval_eq_one
      query strategy word hword.1
  have haction :=
    operatorRefutationWord_observableProfileEval_mulVec_eq_neg
      query sign strategy word hword hperfect
  rw [hevalOne] at haction
  simp only [Matrix.one_mulVec] at haction
  have hampZero : strategy.state.amp = 0 := by
    funext index
    exact CharZero.eq_neg_self_iff.mp (congrFun haction index)
  exact pureVector_amp_ne_zero strategy.state hampZero

end

end XORGame
end QIT

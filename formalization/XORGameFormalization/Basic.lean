/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Init
public import Mathlib.Data.Matrix.Mul

/-!
# Finite XOR-game clause supports

This module records the finite combinatorial data used by the structural
theory of multiplayer XOR games.  A clause chooses one local question for
every player, and its incidence row is the corresponding one-hot vector
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:835-900].
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- An unsigned XOR clause chooses one question for every player. -/
abbrev Clause (Player : Type uP) (Question : Type uQ) :=
  Player → Question

/-- The player type in the four-player, at-most-three-question specialization. -/
abbrev FourByThreePlayer := Fin 4

/-- The question type in the four-player, at-most-three-question specialization. -/
abbrev FourByThreeQuestion := Fin 3

/-- An unsigned clause in the four-player, at-most-three-question specialization. -/
abbrev FourByThreeClause := Clause FourByThreePlayer FourByThreeQuestion

/--
A finite support indexed by `ClauseId`, together with its unsigned clauses.

Injectivity records that the listed clauses are distinct.  Finiteness of all
three index types is supplied by `Fintype` instances at the point of use.
-/
structure FiniteSupport (Player : Type uP) (Question : Type uQ) (ClauseId : Type uC)
    [Fintype Player] [Fintype Question] [Fintype ClauseId] where
  /-- The unsigned question tuple associated to a clause index. -/
  query : ClauseId → Clause Player Question
  /-- Distinct clause indices represent distinct question tuples. -/
  query_injective : Function.Injective query

/--
The integer incidence matrix of a clause family.

Rows are clauses and columns are player-question pairs.  Every row has one
entry equal to one in each player block and zero elsewhere
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:835-900].
-/
def incidence [DecidableEq Question]
    (query : ClauseId → Clause Player Question) :
    Matrix ClauseId (Player × Question) ℤ :=
  fun c pq => if query c pq.1 = pq.2 then 1 else 0

@[simp]
theorem incidence_apply [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (c : ClauseId)
    (p : Player) (q : Question) :
    incidence query c (p, q) = if query c p = q then 1 else 0 := rfl

/--
An integer vector is a relation among the incidence rows when every
player-question coordinate has signed sum zero.
-/
def IsIntegerRelation [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ) : Prop :=
  ∀ pq : Player × Question, ∑ c : ClauseId, incidence query c pq * y c = 0

/-- Matrix form of the integer-relation predicate: `Aᵀ y = 0`. -/
theorem isIntegerRelation_iff_transpose_mulVec [Fintype ClauseId]
    [DecidableEq Question]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ) :
    IsIntegerRelation query y ↔
      Matrix.mulVec (Matrix.transpose (incidence query)) y = 0 := by
  simp only [IsIntegerRelation, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    mul_comm, funext_iff, Pi.zero_apply]

end

end XORGame
end QIT

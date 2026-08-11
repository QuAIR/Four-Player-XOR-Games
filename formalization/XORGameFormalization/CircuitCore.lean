/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Circuit

/-!
# Local structure of a full XOR-game circuit

A question value occurring in exactly one clause is a coloop coordinate: its
incidence column isolates that row.  Hence it cannot occur in a minimally
dependent, full-support circuit.  This is the structural singleton-free fact
used in the boundary page-profile arguments.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/-- The clauses using question `q` on player page `player`. -/
def questionFiber {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (player : Fin 4) (q : Fin 3) : Finset E :=
  Finset.univ.filter fun clause => query clause player = q

@[simp]
theorem mem_questionFiber {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (player : Fin 4) (q : Fin 3) (clause : E) :
    clause ∈ questionFiber query player q ↔ query clause player = q := by
  classical
  simp [questionFiber]

/--
No question fiber of a full rational circuit consists of exactly one clause.
-/
theorem fullCircuit_questionFiber_not_singleton
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (player : Fin 4) (q : Fin 3) (clause₀ : E) :
    questionFiber query player q ≠ {clause₀} := by
  classical
  intro hfiber
  apply hCircuit.1
  apply Fintype.linearIndependent_iffₛ.mpr
  intro left right hsum clause
  have hfiber_iff (e : E) :
      query e player = q ↔ e = clause₀ := by
    have hmem :=
      congrArg (fun fiber : Finset E => e ∈ fiber) hfiber
    simpa using hmem
  have hclause₀ : query clause₀ player = q :=
    (hfiber_iff clause₀).2 rfl
  have hcoefficient : left clause₀ = right clause₀ := by
    have hcoordinate :=
      congrFun hsum (player, q)
    simpa [rationalIncidence, incidence, hfiber_iff] using hcoordinate
  by_cases hclause : clause = clause₀
  · simpa [hclause] using hcoefficient
  · have hsubsum :
        ∑ i : {i : E // i ≠ clause₀},
            left i.1 • (rationalIncidence query).row i.1 =
          ∑ i : {i : E // i ≠ clause₀},
            right i.1 • (rationalIncidence query).row i.1 := by
      rw [Fintype.sum_eq_add_sum_subtype_ne
            (fun i => left i • (rationalIncidence query).row i) clause₀,
          Fintype.sum_eq_add_sum_subtype_ne
            (fun i => right i • (rationalIncidence query).row i) clause₀] at hsum
      exact add_left_cancel
        (hcoefficient ▸ hsum)
    have hsub :=
      Fintype.linearIndependent_iffₛ.mp (hCircuit.2 clause₀)
        (fun i : {i : E // i ≠ clause₀} => left i.1)
        (fun i : {i : E // i ≠ clause₀} => right i.1)
        hsubsum ⟨clause, hclause⟩
    exact hsub

/-- Every nonempty question fiber of a full circuit has at least two clauses. -/
theorem fullCircuit_questionFiber_card_ne_one
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query))
    (player : Fin 4) (q : Fin 3) :
    (questionFiber query player q).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨clause₀, hfiber⟩ :=
    Finset.card_eq_one.mp hcard
  exact fullCircuit_questionFiber_not_singleton
    query hCircuit player q clause₀ hfiber

end

end XORGame
end QIT

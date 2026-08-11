/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank bounds for XOR-game circuits

This module isolates the linear-algebraic reason that a primitive circuit in
a four-player, three-question XOR support has at most ten clauses. The proof
uses only the one-hot column-sum equations of the incidence matrix and no
enumeration of clause supports.

The incidence-matrix model comes from
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:835-900].
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE uC

noncomputable section

/-- The rational incidence matrix used for rank and circuit calculations. -/
def rationalIncidence {E : Type uE}
    (query : E → FourByThreeClause) :
    Matrix E (Fin 4 × Fin 3) ℚ :=
  (incidence query).map (Int.castRingHom ℚ)

/--
Every player block of a four-player, three-question incidence matrix has
row sum one.

This is stated for an arbitrary rational matrix so later structural lemmas
can use only the precise linear invariant they need.
-/
def HasFourByThreeIncidenceSums {E : Type uE}
    (A : Matrix E (Fin 4 × Fin 3) ℚ) : Prop :=
  ∀ e a, ∑ j : Fin 3, A e (a, j) = 1

/-- A concrete four-by-three XOR incidence matrix has the required block sums. -/
theorem rationalIncidence_hasFourByThreeIncidenceSums
    {E : Type uE} (query : E → FourByThreeClause) :
    HasFourByThreeIncidenceSums (rationalIncidence query) := by
  intro e a
  generalize hq : query e a = q
  fin_cases q <;>
    norm_num [rationalIncidence, incidence, Fin.sum_univ_succ, hq, Fin.ext_iff] <;>
    decide

/-- Nine explicit vectors spanning every four-by-three incidence column. -/
private def fourByThreeRankGenerator {E : Type uE}
    (A : Matrix E (Fin 4 × Fin 3) ℚ) :
    Option (Fin 4 × Fin 2) → (E → ℚ)
  | none => fun _ => 1
  | some (a, j) => A.col (a, j.succ)

/--
A rational matrix with four three-column player blocks, each summing rowwise
to one, has rank at most nine.
-/
theorem fourByThree_incidence_rank_le_nine {E : Type uE} [Fintype E]
    (A : Matrix E (Fin 4 × Fin 3) ℚ)
    (hA : HasFourByThreeIncidenceSums A) :
    A.rank ≤ 9 := by
  rw [Matrix.rank_eq_finrank_span_cols]
  calc
    Module.finrank ℚ (Submodule.span ℚ (Set.range A.col)) ≤
        Module.finrank ℚ
          (Submodule.span ℚ (Set.range (fourByThreeRankGenerator A))) := by
      apply Submodule.finrank_mono
      apply Submodule.span_le.2
      rintro _ ⟨⟨a, j⟩, rfl⟩
      refine Fin.cases ?_ (fun j : Fin 2 => ?_) j
      · change A.col (a, 0) ∈
          Submodule.span ℚ (Set.range (fourByThreeRankGenerator A))
        have hnone : fourByThreeRankGenerator A none ∈
            Submodule.span ℚ (Set.range (fourByThreeRankGenerator A)) :=
          Submodule.subset_span ⟨none, rfl⟩
        have hzero : fourByThreeRankGenerator A (some (a, 0)) ∈
            Submodule.span ℚ (Set.range (fourByThreeRankGenerator A)) :=
          Submodule.subset_span ⟨some (a, 0), rfl⟩
        have hone : fourByThreeRankGenerator A (some (a, 1)) ∈
            Submodule.span ℚ (Set.range (fourByThreeRankGenerator A)) :=
          Submodule.subset_span ⟨some (a, 1), rfl⟩
        have heq : A.col (a, 0) =
            fourByThreeRankGenerator A none -
              fourByThreeRankGenerator A (some (a, 0)) -
                fourByThreeRankGenerator A (some (a, 1)) := by
          funext e
          have hsum := hA e a
          simp only [Fin.sum_univ_succ] at hsum
          change A e (a, 0) =
            1 - A e (a, (0 : Fin 2).succ) -
              A e (a, (1 : Fin 2).succ)
          norm_num [Fin.ext_iff] at hsum ⊢
          linarith
        rw [heq]
        exact Submodule.sub_mem _
          (Submodule.sub_mem _ hnone hzero) hone
      · change fourByThreeRankGenerator A (some (a, j)) ∈
          Submodule.span ℚ (Set.range (fourByThreeRankGenerator A))
        exact Submodule.subset_span ⟨some (a, j), rfl⟩
    _ ≤ Fintype.card (Option (Fin 4 × Fin 2)) := by
      simpa only [Set.finrank] using
        (finrank_range_le_card (R := ℚ) (fourByThreeRankGenerator A))
    _ = 9 := by simp

/--
The rows of `A` form a full rational circuit: they are dependent, but deleting
any one row leaves a linearly independent family.
-/
def IsFullRationalCircuit {E : Type uE} {C : Type uC}
    [Fintype E] (A : Matrix E C ℚ) : Prop :=
  ¬ LinearIndependent ℚ A.row ∧
    ∀ e : E,
      LinearIndependent ℚ
        (fun i : {i : E // i ≠ e} => A.row i)

/-- A nonempty full rational circuit has one more row than its matrix rank. -/
theorem fullRationalCircuit_card_eq_rank_add_one
    {E : Type uE} {C : Type uC}
    [Fintype E] [Fintype C] [Nonempty E]
    (A : Matrix E C ℚ) (hA : IsFullRationalCircuit A) :
    Fintype.card E = A.rank + 1 := by
  classical
  let e : E := Classical.choice ‹Nonempty E›
  let A' : Matrix {i : E // i ≠ e} C ℚ :=
    A.submatrix Subtype.val id
  have hLI : LinearIndependent ℚ A'.row := by
    simpa [A', Matrix.submatrix] using hA.2 e
  have hlower : Fintype.card E - 1 ≤ A.rank := by
    calc
      Fintype.card E - 1 = Fintype.card {i : E // i ≠ e} := by simp
      _ = A'.rank := hLI.rank_matrix.symm
      _ ≤ A.rank := by
        simpa [A'] using Matrix.rank_submatrix_le A Subtype.val id
  have hupper : A.rank < Fintype.card E := by
    have hle := A.rank_le_card_height
    refine lt_of_le_of_ne hle ?_
    intro heq
    apply hA.1
    rw [linearIndependent_iff_card_eq_finrank_span,
      ← show A.rank = Set.finrank ℚ (Set.range A.row) from
        A.rank_eq_finrank_span_row]
    exact heq.symm
  omega

/--
Every full primitive circuit in a four-player, three-question XOR incidence
matrix has at most ten clauses. This is the structural `m < 11` cutoff:
sizes eleven, twelve, and all larger sizes require no circuit census.
-/
theorem fourByThree_primitiveCircuit_card_le_ten
    {E : Type uE} [Fintype E] [Nonempty E]
    (A : Matrix E (Fin 4 × Fin 3) ℚ)
    (hIncidence : HasFourByThreeIncidenceSums A)
    (hCircuit : IsFullRationalCircuit A) :
    Fintype.card E ≤ 10 := by
  have hrank := fourByThree_incidence_rank_le_nine A hIncidence
  rw [fullRationalCircuit_card_eq_rank_add_one A hCircuit]
  omega

/-- Concrete XOR-support form of the ten-clause rank cutoff. -/
theorem fourByThree_queryCircuit_card_le_ten
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    Fintype.card E ≤ 10 :=
  fourByThree_primitiveCircuit_card_le_ten
    (rationalIncidence query)
    (rationalIncidence_hasFourByThreeIncidenceSums query)
    hCircuit

end

end XORGame
end QIT

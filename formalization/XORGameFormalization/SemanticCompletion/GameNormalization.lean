/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.FiniteGame
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic

/-!
# Normalization of finite weighted XOR games

This module normalizes a finite weighted game by deleting zero weights,
merging duplicate signed clauses, and resolving the unique positive target
sign of every reduced clause.  The reduced clause index forgets the target
sign while retaining exactly the positive unsigned support.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uC

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

namespace FiniteFourPlayerXORGame

variable (G : FiniteFourPlayerXORGame Question)

/-- The reduced clause index of a no-conflict game: one unsigned question
tuple for every tuple that occurs at positive weight with some target sign. -/
def ReducedClauseId (G : FiniteFourPlayerXORGame Question) : Type uQ :=
  {query : FourPlayerQuestionTuple Question //
    ∃ b : ZMod 2, 0 < G.weight (query, b)}

noncomputable instance reducedClauseId_fintype (G : FiniteFourPlayerXORGame Question) :
    Fintype G.ReducedClauseId := by
  classical
  exact Fintype.subtype
    (Finset.univ.filter (fun query : FourPlayerQuestionTuple Question =>
      ∃ b : ZMod 2, 0 < G.weight (query, b)))
    (by intro query; simp)

/-- Decidable equality on reduced clause ids. -/
noncomputable instance reducedClauseId_decidableEq (G : FiniteFourPlayerXORGame Question) :
    DecidableEq G.ReducedClauseId := by
  classical
  infer_instance

/-- A public `ZMod 2` case split helper. -/
theorem zmodTwo_eq_zero_or_one (x : ZMod 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The unsigned question tuple of a reduced clause. -/
def reducedQuery (G : FiniteFourPlayerXORGame Question)
    (c : G.ReducedClauseId) : Clause (Fin 4) Question :=
  c.1

/-- The unique positive target sign of a reduced clause. -/
noncomputable def reducedSign (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (c : G.ReducedClauseId) : ZMod 2 :=
  Classical.choose c.2

/-- The positive weight of a reduced clause. -/
noncomputable def reducedWeight (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (c : G.ReducedClauseId) : ℝ :=
  G.weight (c.1, G.reducedSign hconflict c)

/-- The reduced sign is supported. -/
theorem reducedSign_supported (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    0 < G.weight (c.1, G.reducedSign hconflict c) :=
  Classical.choose_spec c.2

/-- The reduced sign is the unique positive target sign. -/
theorem reducedSign_unique (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId)
    (b : ZMod 2) (hpos : 0 < G.weight (c.1, b)) :
    b = G.reducedSign hconflict c := by
  by_contra hne
  rcases zmodTwo_eq_zero_or_one b with rfl | rfl
  · rcases zmodTwo_eq_zero_or_one (G.reducedSign hconflict c) with hsign | hsign
    · exact hne hsign.symm
    ·
      exact False.elim
        (hconflict ⟨c.1, hpos,
          by simpa [hsign] using G.reducedSign_supported hconflict c⟩)
  · rcases zmodTwo_eq_zero_or_one (G.reducedSign hconflict c) with hsign | hsign
    ·
      exact False.elim
        (hconflict ⟨c.1,
          by simpa [hsign] using G.reducedSign_supported hconflict c, hpos⟩)
    · exact hne hsign.symm

/-- The reduced weight is strictly positive. -/
theorem reducedWeight_pos (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    0 < G.reducedWeight hconflict c :=
  G.reducedSign_supported hconflict c

/-- The reduced clause map is injective. -/
theorem reducedQuery_injective (G : FiniteFourPlayerXORGame Question) :
    Function.Injective (G.reducedQuery) := by
  intro c₁ c₂ h
  exact Subtype.ext h

/-- The signed representative of a reduced clause in the raw support. -/
noncomputable def reducedSignedClause (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (c : G.ReducedClauseId) : SignedFourPlayerClause Question :=
  (c.1, G.reducedSign hconflict c)

/-- Every reduced signed representative lies in the raw support. -/
theorem reducedSignedClause_mem_support
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) (c : G.ReducedClauseId) :
    G.reducedSignedClause hconflict c ∈ G.support := by
  rw [mem_support_iff]
  exact G.reducedSign_supported hconflict c

/-- The reduced signed representatives are pairwise distinct. -/
theorem reducedSignedClause_injective
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    Function.Injective (G.reducedSignedClause hconflict) := by
  intro c₁ c₂ h
  apply Subtype.ext
  exact congrArg Prod.fst h

/-- Every raw support clause is represented by exactly one reduced clause. -/
theorem raw_support_eq_reduced_support
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    G.support =
      (Finset.univ.image (G.reducedSignedClause hconflict) :
        Finset (SignedFourPlayerClause Question)) := by
  classical
  apply Finset.Subset.antisymm
  · intro raw hraw
    rw [mem_support_iff] at hraw
    rcases raw with ⟨query, b⟩
    have hred : G.ReducedClauseId := ⟨query, b, hraw⟩
    have hb : b = G.reducedSign hconflict ⟨query, b, hraw⟩ :=
      G.reducedSign_unique hconflict ⟨query, b, hraw⟩ b hraw
    rw [Finset.mem_image]
    exact ⟨⟨query, b, hraw⟩, Finset.mem_univ _, by
      simp [reducedSignedClause, hb]⟩
  · intro raw hraw
    rw [Finset.mem_image] at hraw
    rcases hraw with ⟨c, hc, rfl⟩
    exact G.reducedSignedClause_mem_support hconflict c

/-- The reduced weights sum to one. -/
theorem reducedWeight_sum_one (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets) :
    (∑ c : G.ReducedClauseId, G.reducedWeight hconflict c) = 1 := by
  classical
  have himage :
      (∑ c : G.ReducedClauseId,
          G.weight (G.reducedSignedClause hconflict c)) =
        (∑ raw ∈ (Finset.univ.image (G.reducedSignedClause hconflict) :
            Finset (SignedFourPlayerClause Question)), G.weight raw) := by
    rw [← Finset.sum_image
      (g := G.reducedSignedClause hconflict) (f := G.weight)
      (Set.injOn_of_injective (G.reducedSignedClause_injective hconflict))]
  have htotal :
      (∑ raw : SignedFourPlayerClause Question, G.weight raw) =
        ∑ raw ∈ G.support, G.weight raw := by
    refine (Finset.sum_subset ?hsubset ?hzero).symm
    · exact Finset.subset_univ _
    · intro raw hraw hnot
      have hnotpos : ¬ 0 < G.weight raw := by
        intro hpos
        exact hnot ((G.mem_support_iff raw).mpr hpos)
      exact le_antisymm (not_lt.mp hnotpos) (G.weight_nonneg raw)
  calc
    (∑ c : G.ReducedClauseId, G.reducedWeight hconflict c)
        = ∑ c : G.ReducedClauseId,
            G.weight (G.reducedSignedClause hconflict c) := by
          rfl
    _ = ∑ raw ∈ (Finset.univ.image (G.reducedSignedClause hconflict) :
            Finset (SignedFourPlayerClause Question)), G.weight raw := himage
    _ = ∑ raw ∈ G.support, G.weight raw := by
          rw [G.raw_support_eq_reduced_support hconflict]
    _ = ∑ raw : SignedFourPlayerClause Question, G.weight raw := htotal.symm
    _ = 1 := G.weight_sum_one

/-- Perfection over the raw support is equivalent to perfection over the
reduced support, for any clause-satisfaction predicate. -/
theorem perfectOnRawSupport_iff_perfectOnReducedSupport
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (wins : SignedFourPlayerClause Question → Prop) :
    (∀ clause, clause ∈ G.support → wins clause) ↔
      (∀ c : G.ReducedClauseId,
        wins (c.1, G.reducedSign hconflict c)) := by
  constructor
  · intro hperfect c
    exact hperfect (c.1, G.reducedSign hconflict c)
      (G.reducedSignedClause_mem_support hconflict c)
  · intro hreduced clause hclause
    rw [G.raw_support_eq_reduced_support hconflict] at hclause
    rw [Finset.mem_image] at hclause
    rcases hclause with ⟨c, hc, rfl⟩
    exact hreduced c

/-- A deterministic clause-satisfaction predicate cannot be satisfied on both
positive targets of a conflicting query. -/
theorem conflictingTargets_exclude_deterministic_clause_satisfaction
    (G : FiniteFourPlayerXORGame Question)
    (wins : SignedFourPlayerClause Question → Prop)
    (hconflict : G.HasConflictingTargets)
    (hdeterministic : ∀ query, ¬ (wins (query, (0 : ZMod 2)) ∧
      wins (query, (1 : ZMod 2)))) :
    ¬ (∀ clause, clause ∈ G.support → wins clause) := by
  rintro hperfect
  rcases hconflict with ⟨query, hzero, hone⟩
  exact hdeterministic query
    ⟨hperfect (query, (0 : ZMod 2)) ((G.mem_support_iff _).mpr hzero),
     hperfect (query, (1 : ZMod 2)) ((G.mem_support_iff _).mpr hone)⟩

/-- `ofIndexed` perfection is invariant under deleting zero weights and
merging repeated indexed clauses with the same sign. -/
theorem ofIndexed_perfectOnSupport_iff_perfectOnIndexed
    {ClauseId : Type uC} [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → FourPlayerQuestionTuple Question)
    (sign : ClauseId → ZMod 2)
    (weight : ClauseId → ℝ)
    (hweight_nonneg : ∀ c, 0 ≤ weight c)
    (hweight_sum_one : ∑ c, weight c = 1)
    (wins : SignedFourPlayerClause Question → Prop) :
    (∀ clause,
      clause ∈ (ofIndexed query sign weight hweight_nonneg hweight_sum_one).support →
        wins clause) ↔
      (∀ c : ClauseId, weight c ≠ 0 → wins (query c, sign c)) := by
  classical
  constructor
  · intro hperfect c hc_ne
    have hposweight : 0 < weight c :=
      lt_of_le_of_ne (hweight_nonneg c) (Ne.symm hc_ne)
    have hle :
        weight c ≤
          (∑ d : ClauseId,
            if query d = query c ∧ sign d = sign c then weight d else 0) := by
      have hsingle := Finset.single_le_sum
        (s := (Finset.univ : Finset ClauseId))
        (f := fun d : ClauseId =>
          if query d = query c ∧ sign d = sign c then weight d else 0)
        (a := c) ?_ (Finset.mem_univ c)
      · simpa using hsingle
      · intro d hd
        by_cases h : query d = query c ∧ sign d = sign c
        · simp [h, hweight_nonneg d]
        · simp [h]
    have hposSum : 0 <
        (∑ d : ClauseId,
          if query d = query c ∧ sign d = sign c then weight d else 0) :=
      lt_of_lt_of_le hposweight hle
    rw [← ofIndexed_weight query sign weight hweight_nonneg hweight_sum_one
      (query c, sign c)] at hposSum
    exact hperfect (query c, sign c)
      ((mem_support_iff _ _).mpr hposSum)
  · intro hindexed clause hclause
    rw [mem_support_iff] at hclause
    rw [ofIndexed_weight] at hclause
    by_contra hnot
    have hsum_zero :
        (∑ d : ClauseId,
          if query d = clause.1 ∧ sign d = clause.2 then weight d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      by_cases h : query d = clause.1 ∧ sign d = clause.2
      · have hzero : weight d = 0 := by
          by_contra hne
          exact hnot (by simpa [h.1, h.2] using hindexed d hne)
        simp [h, hzero]
      · simp [h]
    rw [hsum_zero] at hclause
    norm_num at hclause

end FiniteFourPlayerXORGame

/-! ## Conflict example -/

namespace GameNormalizationExamples

abbrev Q3 := Fin 3
abbrev C2 := Fin 2

/-- Both indices point to the same query with opposite target signs. -/
def conflictQuery : C2 → FourPlayerQuestionTuple Q3 :=
  fun _ _ => (0 : Q3)

def conflictSign : C2 → ZMod 2 :=
  fun c => if c = 0 then (0 : ZMod 2) else (1 : ZMod 2)

theorem conflictQuery_zero : conflictQuery 0 = (fun _ : Fin 4 => (0 : Q3)) := by
  funext p
  simp [conflictQuery]

theorem conflictQuery_one : conflictQuery 1 = (fun _ : Fin 4 => (0 : Q3)) := by
  funext p
  simp [conflictQuery]

theorem conflictSign_zero : conflictSign 0 = (0 : ZMod 2) := by
  simp [conflictSign]

theorem conflictSign_one : conflictSign 1 = (1 : ZMod 2) := by
  simp [conflictSign]

def conflictWeight : C2 → ℝ :=
  fun _ => (1 / 2 : ℝ)

theorem conflictWeight_nonneg : ∀ c : C2, 0 ≤ conflictWeight c := by
  intro c
  unfold conflictWeight
  positivity

theorem conflictWeight_sum_one : (∑ c : C2, conflictWeight c) = 1 := by
  simp [conflictWeight, Fin.sum_univ_succ]

noncomputable def conflictGame : FiniteFourPlayerXORGame Q3 :=
  FiniteFourPlayerXORGame.ofIndexed conflictQuery conflictSign conflictWeight
    conflictWeight_nonneg conflictWeight_sum_one

example : conflictGame.HasConflictingTargets := by
  unfold conflictGame FiniteFourPlayerXORGame.HasConflictingTargets
  refine ⟨fun _ => (0 : Q3), ?_, ?_⟩
  · rw [FiniteFourPlayerXORGame.ofIndexed_weight]
    simp [conflictQuery_zero, conflictQuery_one, conflictSign_zero,
      conflictSign_one, conflictWeight, Fin.sum_univ_succ]
  · rw [FiniteFourPlayerXORGame.ofIndexed_weight]
    simp [conflictQuery_zero, conflictQuery_one, conflictSign_zero,
      conflictSign_one, conflictWeight, Fin.sum_univ_succ]

/-- A game with only same-sign duplicates of one unsigned query. -/
def sameSignQuery : C2 → FourPlayerQuestionTuple Q3 :=
  fun _ _ => (0 : Q3)

def sameSignSign : C2 → ZMod 2 :=
  fun _ => (0 : ZMod 2)

theorem sameSignQuery_eq (c : C2) :
    sameSignQuery c = (fun _ : Fin 4 => (0 : Q3)) := by
  funext p
  simp [sameSignQuery]

theorem sameSignSign_zero : sameSignSign 0 = (0 : ZMod 2) := by
  simp [sameSignSign]

theorem sameSignSign_one : sameSignSign 1 = (0 : ZMod 2) := by
  simp [sameSignSign]

def sameSignWeight : C2 → ℝ :=
  fun _ => (1 / 2 : ℝ)

theorem sameSignWeight_nonneg : ∀ c : C2, 0 ≤ sameSignWeight c := by
  intro c
  unfold sameSignWeight
  positivity

theorem sameSignWeight_sum_one : (∑ c : C2, sameSignWeight c) = 1 := by
  simp [sameSignWeight, Fin.sum_univ_succ]

noncomputable def sameSignGame : FiniteFourPlayerXORGame Q3 :=
  FiniteFourPlayerXORGame.ofIndexed sameSignQuery sameSignSign sameSignWeight
    sameSignWeight_nonneg sameSignWeight_sum_one

/-- Every reduced clause of the same-sign duplicate game is the constant zero
tuple. -/
theorem sameSignGame_reduced_query_eq_zero
    (c : sameSignGame.ReducedClauseId) :
    c.1 = (fun _ : Fin 4 => (0 : Q3)) := by
  classical
  by_contra hne
  rcases c.2 with ⟨b, hpos⟩
  simp [sameSignGame, FiniteFourPlayerXORGame.ofIndexed_weight] at hpos
  have hsum_zero :
      (∑ d : C2,
        if sameSignQuery d = c.1 ∧ sameSignSign d = b
          then sameSignWeight d else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro d hd
    have hnot : ¬ (sameSignQuery d = c.1 ∧ sameSignSign d = b) := by
      intro h
      exact hne (by simpa [sameSignQuery] using h.1.symm)
    simp [hnot]
  have hsum_zero_explicit :
      (if sameSignQuery 0 = c.1 ∧ sameSignSign 0 = b
          then sameSignWeight 0 else 0) +
        (if sameSignQuery 1 = c.1 ∧ sameSignSign 1 = b
          then sameSignWeight 1 else 0) = 0 := by
    simpa [Fin.sum_univ_succ] using hsum_zero
  rw [hsum_zero_explicit] at hpos
  norm_num at hpos

/-- The same-sign duplicate game has exactly one reduced clause. -/
example : Fintype.card sameSignGame.ReducedClauseId = 1 := by
  classical
  refine Fintype.card_congr
    (α := sameSignGame.ReducedClauseId) (β := Unit) ?_
  refine
    { toFun := fun _ => ()
      invFun := fun _ => ⟨fun _ => (0 : Q3), ⟨(0 : ZMod 2), ?_⟩⟩
      left_inv := fun c => by
        apply Subtype.ext
        exact (sameSignGame_reduced_query_eq_zero c).symm
      right_inv := fun u => by
        cases u
        rfl }
  · simp [sameSignGame, FiniteFourPlayerXORGame.ofIndexed_weight,
      sameSignQuery_eq, sameSignSign_zero, sameSignSign_one,
      sameSignWeight, Fin.sum_univ_succ]

end GameNormalizationExamples

end

end XORGame
end QIT

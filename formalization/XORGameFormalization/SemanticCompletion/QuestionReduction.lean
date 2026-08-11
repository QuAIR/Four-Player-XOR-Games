/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SemanticCompletion.GameNormalization
public import XORGameFormalization.Spaces
public import XORGameFormalization.StructuralWindows
public import XORGameFormalization.Main
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

/-!
# Reduction of active question alphabets to `Fin 3`

This module removes the artificial assumption that the ambient question type
is exactly `Fin 3`.  Player-dependent encodings that are injective on each
player's active questions transport the combinatorial PREF/refutation and
parity notions to the already-proved four-by-three structural theorem.
-/

@[expose] public section

open scoped BigOperators

namespace QIT
namespace XORGame

universe uQ uA uB

noncomputable section

variable {Question : Type uQ} [Fintype Question] [DecidableEq Question]

namespace InvolutionWord

private lemma split_of_map_eq_append_cons_cons {α : Type uA} {β : Type uB} {f : α → β}
    {S : Set α} (hf : Set.InjOn f S) {word : List α} {left right : List β} {a : β}
    (hword : ∀ x ∈ word, x ∈ S)
    (h : word.map f = left ++ a :: a :: right) :
    ∃ (wl wr : List α) (x : α),
      word = wl ++ x :: x :: wr ∧
        wl.map f = left ∧ wr.map f = right ∧ f x = a := by
  classical
  let n := left.length
  have hword_len : n < word.length := by
    have h' : n < (word.map f).length := by
      rw [h]
      simp [n]
    simpa using h'
  have hlen : n + 1 < word.length := by
    have h' : n + 1 < (word.map f).length := by
      rw [h]
      simp [n]
    simpa using h'
  let wl := word.take n
  let x : α := word[n]'hword_len
  let wr := word.drop (n + 2)
  have hmap_len : n < (word.map f).length := by simpa using hword_len
  have hmap_len1 : n + 1 < (word.map f).length := by simpa using hlen
  have hx_in : word[n]'hword_len ∈ S := hword (word[n]'hword_len) (List.getElem_mem hword_len)
  have hx1_in : word[n + 1]'hlen ∈ S := hword (word[n + 1]'hlen) (List.getElem_mem hlen)
  have hx_eq : word[n]'hword_len = word[n + 1]'hlen := by
    have hcomp0 : GetElem.getElem (word.map f) n hmap_len = a := by
      have hq : (word.map f)[n]? = some a := by
        rw [h]
        simp [n]
      have hs := (List.getElem?_eq_getElem hmap_len).symm.trans hq
      simpa using hs
    have hcomp1 : GetElem.getElem (word.map f) (n + 1) hmap_len1 = a := by
      have hq : (word.map f)[n + 1]? = some a := by
        rw [h]
        simp [n]
      have hs := (List.getElem?_eq_getElem hmap_len1).symm.trans hq
      simpa using hs
    have hmap0 : GetElem.getElem (word.map f) n hmap_len = f (word[n]'hword_len) :=
      List.getElem_map f (l := word) (i := n) (h := hmap_len)
    have hmap1 : GetElem.getElem (word.map f) (n + 1) hmap_len1 = f (word[n + 1]'hlen) :=
      List.getElem_map f (l := word) (i := n + 1) (h := hmap_len1)
    have hf0 : f (word[n]'hword_len) = a := by
      rw [hmap0] at hcomp0
      exact hcomp0
    have hf1 : f (word[n + 1]'hlen) = a := by
      rw [hmap1] at hcomp1
      exact hcomp1
    exact hf hx_in hx1_in (by rw [hf0, hf1])
  refine ⟨wl, wr, x, ?_, ?_, ?_, ?_⟩
  · calc
      word = word.take n ++ word.drop n := (List.take_append_drop n word).symm
      _ = word.take n ++ (word[n]'hword_len :: word.drop (n + 1)) := by
          rw [List.drop_eq_getElem_cons hword_len]
      _ = word.take n ++ (word[n]'hword_len :: word[n + 1]'hlen :: word.drop (n + 2)) := by
          congr 1
          rw [← List.cons_getElem_drop_succ (l := word) (n := n + 1) (h := hlen)]
      _ = wl ++ x :: x :: wr := by
          simp [wl, x, wr, hx_eq]
  · calc
      wl.map f = (word.map f).take n := by simp [wl, List.map_take]
      _ = (left ++ a :: a :: right).take n := by rw [h]
      _ = left := by simp [n]
  · calc
      wr.map f = (word.map f).drop (n + 2) := by simp [wr, List.map_drop]
      _ = (left ++ a :: a :: right).drop (n + 2) := by rw [h]
      _ = right := by simp [n]
  · have hcomp0 : GetElem.getElem (word.map f) n hmap_len = a := by
      have hq : (word.map f)[n]? = some a := by
        rw [h]
        simp [n]
      have hs := (List.getElem?_eq_getElem hmap_len).symm.trans hq
      simpa using hs
    have hmap0 : GetElem.getElem (word.map f) n hmap_len = f (word[n]'hword_len) :=
      List.getElem_map f (l := word) (i := n) (h := hmap_len)
    rw [hmap0] at hcomp0
    exact hcomp0

/-- Mapping letters preserves reducibility to the empty word. -/
private theorem reducesToEmpty_map {α : Type uA} {β : Type uB} (f : α → β)
    {word : List α} (h : ReducesToEmpty word) : ReducesToEmpty (word.map f) := by
  induction h with
  | nil => exact ReducesToEmpty.nil
  | insert left right letter reduced ih =>
      simp only [List.map_append, List.map_cons]
      simpa [List.map_append] using ReducesToEmpty.insert (left.map f) (right.map f) (f letter)
        (by simpa [List.map_append] using ih)

/-- An injective-on-support letter map reflects reducibility to the empty word. -/
private theorem reducesToEmpty_of_map_of_injOn {α : Type uA} {β : Type uB} {f : α → β}
    {S : Set α} (hf : Set.InjOn f S) {word : List α}
    (hword : ∀ x ∈ word, x ∈ S) (h : ReducesToEmpty (word.map f)) :
    ReducesToEmpty word := by
  have helper :
      ∀ {word : List α} {l : List β}, l = word.map f →
        (∀ x ∈ word, x ∈ S) → ReducesToEmpty l → ReducesToEmpty word := by
    intro word l hl hword h
    induction h generalizing word with
    | nil =>
        cases word with
        | nil => exact .nil
        | cons a as =>
            have hnil : (a :: as).map f = [] := hl.symm
            simp at hnil
    | insert left right a reduced ih =>
        have hmap : word.map f = left ++ a :: a :: right := hl.symm
        rcases split_of_map_eq_append_cons_cons hf hword hmap with
          ⟨wl, wr, x, hword_eq, hwl, hwr, hfx⟩
        have hred : left ++ right = (wl ++ wr).map f := by
          rw [List.map_append, hwl, hwr]
        have hsub : ∀ y ∈ wl ++ wr, y ∈ S := by
          intro y hy
          exact hword y (by
            rw [hword_eq]
            simp [List.mem_append] at hy ⊢
            rcases hy with hy | hy
            · exact Or.inl hy
            · exact Or.inr (Or.inr hy))
        have ihred : ReducesToEmpty (wl ++ wr) := ih hred hsub
        simpa [hword_eq] using (ReducesToEmpty.insert wl wr x ihred)
  exact helper rfl hword h

end InvolutionWord

namespace FiniteFourPlayerXORGame

variable (G : FiniteFourPlayerXORGame Question)

/--
The player-dependent encoding of a question into `Fin 3`.  On each player's
active set it is the `Finset.equivFin` bijection followed by `Fin.castLE`;
inactive questions are sent to `0`.
-/
noncomputable def questionCode
    (hbound : G.activeQuestionBound ≤ 3) (p : Fin 4) (q : Question) : Fin 3 :=
  if hq : q ∈ G.activeQuestions p then
    Fin.castLE
      ((G.activeQuestionBound_le_iff 3).mp hbound p)
      ((G.activeQuestions p).equivFin ⟨q, hq⟩)
  else 0

/-- The encoding is injective on each player's active questions. -/
theorem questionCode_injective_on_activeQuestions
    (hbound : G.activeQuestionBound ≤ 3) (p : Fin 4) :
    Set.InjOn (G.questionCode hbound p) (G.activeQuestions p) := by
  intro q hq r hr hcode
  unfold questionCode at hcode
  have hq' : q ∈ G.activeQuestions p := by simpa using hq
  have hr' : r ∈ G.activeQuestions p := by simpa using hr
  rw [dif_pos hq', dif_pos hr'] at hcode
  have hcast :=
    Fin.castLE_injective ((G.activeQuestionBound_le_iff 3).mp hbound p) hcode
  have hfin : (G.activeQuestions p).equivFin ⟨q, hq⟩ =
      (G.activeQuestions p).equivFin ⟨r, hr⟩ := hcast
  have heq : (⟨q, hq⟩ : G.activeQuestions p) = ⟨r, hr⟩ :=
    (G.activeQuestions p).equivFin.injective hfin
  exact congrArg Subtype.val heq

/-- The encoded clause map is injective on reduced clauses. -/
theorem questionCode_query_injective_on_reducedClauseId
    (hbound : G.activeQuestionBound ≤ 3) :
    Function.Injective
      (fun c : G.ReducedClauseId =>
        fun p : Fin 4 => G.questionCode hbound p (G.reducedQuery c p)) := by
  intro c d h
  apply Subtype.ext
  funext p
  have hc : G.reducedQuery c p ∈ G.activeQuestions p := by
    rcases c.2 with ⟨b, hpos⟩
    exact (G.mem_activeQuestions_iff p (G.reducedQuery c p)).mpr
      ⟨(c.1, b), hpos, rfl⟩
  have hd : G.reducedQuery d p ∈ G.activeQuestions p := by
    rcases d.2 with ⟨b, hpos⟩
    exact (G.mem_activeQuestions_iff p (G.reducedQuery d p)).mpr
      ⟨(d.1, b), hpos, rfl⟩
  exact G.questionCode_injective_on_activeQuestions hbound p hc hd
    (congrFun h p)

/-- The encoded reduced clause map into `FourByThreeClause`. -/
noncomputable def encodedReducedQuery
    (hbound : G.activeQuestionBound ≤ 3) :
    G.ReducedClauseId → FourByThreeClause :=
  fun c p => G.questionCode hbound p (G.reducedQuery c p)

/-- The encoded reduced clause map is injective. -/
theorem encodedReducedQuery_injective
    (hbound : G.activeQuestionBound ≤ 3) :
    Function.Injective (G.encodedReducedQuery hbound) :=
  G.questionCode_query_injective_on_reducedClauseId hbound

/-- Every reduced clause coordinate is an active question for that player. -/
private theorem reducedQuery_letter_mem_active (G : FiniteFourPlayerXORGame Question)
    (p : Fin 4) (c : G.ReducedClauseId) :
    G.reducedQuery c p ∈ G.activeQuestions p := by
  rcases c.2 with ⟨b, hpos⟩
  exact (G.mem_activeQuestions_iff p (G.reducedQuery c p)).mpr
    ⟨(c.1, b), hpos, rfl⟩

private theorem encoded_word_eq_map (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) (p : Fin 4)
    (word : List G.ReducedClauseId) :
    word.map (fun c => G.encodedReducedQuery hbound c p) =
      (word.map (fun c => G.reducedQuery c p)).map
        (fun q => G.questionCode hbound p q) := by
  simp [encodedReducedQuery, List.map_map, Function.comp_def]

private theorem reducesToEmpty_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) (p : Fin 4)
    (word : List G.ReducedClauseId) :
    InvolutionWord.ReducesToEmpty (word.map (fun c => G.reducedQuery c p)) ↔
      InvolutionWord.ReducesToEmpty
        (word.map (fun c => G.encodedReducedQuery hbound c p)) := by
  constructor
  · intro h
    rw [encoded_word_eq_map]
    exact InvolutionWord.reducesToEmpty_map (G.questionCode hbound p) h
  · intro h
    rw [encoded_word_eq_map] at h
    exact InvolutionWord.reducesToEmpty_of_map_of_injOn
      (G.questionCode_injective_on_activeQuestions hbound p) (by
        intro q hq
        rcases List.mem_map.mp hq with ⟨c, hc, rfl⟩
        exact G.reducedQuery_letter_mem_active p c) h

/-- A clause word is balanced exactly when its encoded clause word is balanced. -/
theorem isBalancedWord_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) (word : List G.ReducedClauseId) :
    IsBalancedWord G.reducedQuery word ↔
      IsBalancedWord (G.encodedReducedQuery hbound) word := by
  constructor
  · intro h p
    exact (G.reducesToEmpty_iff_encoded hbound p word).mp (h p)
  · intro h p
    exact (G.reducesToEmpty_iff_encoded hbound p word).mpr (h p)

/-- An integer relation is exactly an integer relation of the encoded clauses. -/
theorem isIntegerRelation_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hbound : G.activeQuestionBound ≤ 3) (y : G.ReducedClauseId → ℤ) :
    IsIntegerRelation G.reducedQuery y ↔
      IsIntegerRelation (G.encodedReducedQuery hbound) y := by
  constructor
  · intro hrel pq
    rcases pq with ⟨p, q'⟩
    by_cases hq : ∃ q ∈ G.activeQuestions p, G.questionCode hbound p q = q'
    · rcases hq with ⟨q, hqmem, hqcode⟩
      have hsum : (∑ c : G.ReducedClauseId,
            incidence (G.encodedReducedQuery hbound) c (p, q') * y c) =
          (∑ c : G.ReducedClauseId, incidence G.reducedQuery c (p, q) * y c) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hiff : G.encodedReducedQuery hbound c p = q' ↔ G.reducedQuery c p = q := by
          constructor
          · intro hcode
            exact G.questionCode_injective_on_activeQuestions hbound p
              (G.reducedQuery_letter_mem_active p c) hqmem (by
                rw [hqcode, ← hcode]
                simp [encodedReducedQuery])
          · intro heq
            simp [encodedReducedQuery, heq, hqcode]
        simpa [hiff]
      rw [hsum]
      exact hrel (p, q)
    · have hzero : ∀ c : G.ReducedClauseId,
          incidence (G.encodedReducedQuery hbound) c (p, q') = 0 := by
        intro c
        rw [incidence_apply]
        by_cases hcode : G.encodedReducedQuery hbound c p = q'
        · exfalso
          exact hq ⟨G.reducedQuery c p, G.reducedQuery_letter_mem_active p c, by
            simpa [encodedReducedQuery] using hcode⟩
        · simp [hcode]
      simp [hzero]
  · intro hrel pq
    rcases pq with ⟨p, q⟩
    by_cases hq : q ∈ G.activeQuestions p
    · let q' := G.questionCode hbound p q
      have hsum : (∑ c : G.ReducedClauseId,
            incidence G.reducedQuery c (p, q) * y c) =
          (∑ c : G.ReducedClauseId,
            incidence (G.encodedReducedQuery hbound) c (p, q') * y c) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hiff : G.reducedQuery c p = q ↔ G.encodedReducedQuery hbound c p = q' := by
          constructor
          · intro heq
            simp [encodedReducedQuery, heq, q']
          · intro hcode
            exact G.questionCode_injective_on_activeQuestions hbound p
              (G.reducedQuery_letter_mem_active p c) hq (by
                simp [encodedReducedQuery, q'] at hcode ⊢
                exact hcode)
        simpa [hiff]
      rw [hsum]
      exact hrel (p, q')
    · have hzero : ∀ c : G.ReducedClauseId, incidence G.reducedQuery c (p, q) = 0 := by
        intro c
        rw [incidence_apply]
        by_cases heq : G.reducedQuery c p = q
        · exfalso
          exact hq (by simpa [heq] using G.reducedQuery_letter_mem_active p c)
        · simp [heq]
      simp [hzero]

/-- PREF existence is preserved by the player-dependent encoding. -/
theorem hasPREF_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) :
    HasPREF G.reducedQuery (G.reducedSign hconflict) ↔
      HasPREF (G.encodedReducedQuery hbound) (G.reducedSign hconflict) := by
  constructor
  · rintro ⟨y, hyrel, hypar⟩
    exact ⟨y, (G.isIntegerRelation_iff_encoded hbound y).mp hyrel, hypar⟩
  · rintro ⟨y, hyrel, hypar⟩
    exact ⟨y, (G.isIntegerRelation_iff_encoded hbound y).mpr hyrel, hypar⟩

/-- Operator-refutation existence is preserved by the player-dependent encoding. -/
theorem isOperatorRefutation_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) (word : List G.ReducedClauseId) :
    IsOperatorRefutation G.reducedQuery (G.reducedSign hconflict) word ↔
      IsOperatorRefutation (G.encodedReducedQuery hbound)
        (G.reducedSign hconflict) word := by
  constructor
  · intro h
    exact ⟨(G.isBalancedWord_iff_encoded hbound word).mp h.1, h.2⟩
  · intro h
    exact ⟨(G.isBalancedWord_iff_encoded hbound word).mpr h.1, h.2⟩

/-- Operator-refutation existence is preserved by the player-dependent encoding. -/
theorem hasOperatorRefutation_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) :
    HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) ↔
      HasOperatorRefutation (G.encodedReducedQuery hbound)
        (G.reducedSign hconflict) := by
  constructor
  · rintro ⟨word, hword⟩
    exact ⟨word, (G.isOperatorRefutation_iff_encoded hconflict hbound word).mp hword⟩
  · rintro ⟨word, hword⟩
    exact ⟨word, (G.isOperatorRefutation_iff_encoded hconflict hbound word).mpr hword⟩

/-- MERP parity is preserved by the player-dependent encoding. -/
theorem isMERPPerfectParity_iff_encoded (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) :
    IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict) ↔
      IsMERPPerfectParity (G.encodedReducedQuery hbound)
        (G.reducedSign hconflict) := by
  rw [isMERPPerfectParity_iff_not_hasPREF, isMERPPerfectParity_iff_not_hasPREF]
  exact not_congr (G.hasPREF_iff_encoded hconflict hbound)

/-- With at most three active questions per player, every PREF of the reduced
clauses has a true operator refutation. -/
theorem operatorRefutation_of_pref_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) :
    HasPREF G.reducedQuery (G.reducedSign hconflict) →
      HasOperatorRefutation G.reducedQuery (G.reducedSign hconflict) := by
  intro hpref
  have hpref' : HasPREF (G.encodedReducedQuery hbound)
      (G.reducedSign hconflict) :=
    (G.hasPREF_iff_encoded hconflict hbound).mp hpref
  have href' : HasOperatorRefutation (G.encodedReducedQuery hbound)
      (G.reducedSign hconflict) :=
    operatorRefutation_of_pref_of_primitiveCircuit_lifts
      (G.encodedReducedQuery hbound) (G.reducedSign hconflict)
      (primitiveCircuit_lifts_fourByThree (G.encodedReducedQuery hbound)
        (G.encodedReducedQuery_injective hbound))
      hpref'
  exact (G.hasOperatorRefutation_iff_encoded hconflict hbound).mpr href'

/-- With at most three active questions per player, commuting perfection parity
implies MERP perfection parity. -/
theorem isCommutingPerfectParity_implies_isMERPPerfectParity_of_activeQuestionBound_le_three
    (G : FiniteFourPlayerXORGame Question)
    (hconflict : ¬ G.HasConflictingTargets)
    (hbound : G.activeQuestionBound ≤ 3) :
    IsCommutingPerfectParity G.reducedQuery (G.reducedSign hconflict) →
      IsMERPPerfectParity G.reducedQuery (G.reducedSign hconflict) := by
  intro hcomm
  have hnoref : ¬ HasOperatorRefutation G.reducedQuery
      (G.reducedSign hconflict) :=
    (isCommutingPerfectParity_iff_not_hasOperatorRefutation
      G.reducedQuery (G.reducedSign hconflict)).mp hcomm
  have hnopref : ¬ HasPREF G.reducedQuery (G.reducedSign hconflict) := by
    intro hpref
    exact hnoref (G.operatorRefutation_of_pref_of_activeQuestionBound_le_three
      hconflict hbound hpref)
  exact (isMERPPerfectParity_iff_not_hasPREF
    G.reducedQuery (G.reducedSign hconflict)).mpr hnopref

end FiniteFourPlayerXORGame

end

end XORGame
end QIT

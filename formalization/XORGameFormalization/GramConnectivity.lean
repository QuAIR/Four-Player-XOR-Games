/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.TenBallCover
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The centered-incidence Gram obstruction at ten clauses

This module supplies the linear-algebraic bridge left by the structural
ten-ball-cover argument.  A rational centered feature has three constant
coordinates and twelve centered question coordinates.  Its Gram entry is

`9 * (3 - d_H(x,y))`.

The feature transpose and the ordinary incidence transpose have the same
kernel.  A full rational circuit therefore forces the off-diagonal nonzero
Gram graph to be connected: restricting a nonzero circuit relation to one
connected component would otherwise produce a nonzero relation with a zero
coordinate.  The connected ten-vertex graph has at least nine edges, in
contradiction with the six-edge upper bound for a ten-ball cover.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE

noncomputable section

/--
Three copies of the constant feature, followed by the twelve centered
player-question indicators.
-/
abbrev CenteredFeatureColumn :=
  Fin 3 ⊕ (FourByThreePlayer × FourByThreeQuestion)

/--
The scaled rational centered-incidence feature.

Constant columns have value `1`; a player-question column has value
`3 * 1_{q_e(a)=q} - 1`.  Three constant copies give the scaled
centered-incidence Gram used below.
-/
def centeredIncidenceFeature {E : Type uE}
    (query : E → FourByThreeClause) :
    Matrix E CenteredFeatureColumn ℚ
  | _, Sum.inl _ => 1
  | e, Sum.inr aq => 3 * rationalIncidence query e aq - 1

/-- The Gram matrix of the scaled centered-incidence feature. -/
def centeredIncidenceGram {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) : Matrix E E ℚ :=
  centeredIncidenceFeature query *
    (centeredIncidenceFeature query).transpose

/-- Entrywise form of the rational incidence matrix. -/
@[simp]
private theorem rationalIncidence_apply'
    {E : Type uE} (query : E → FourByThreeClause)
    (e : E) (page : FourByThreePlayer)
    (question : FourByThreeQuestion) :
    rationalIncidence query e (page, question) =
      if query e page = question then 1 else 0 := by
  simp [rationalIncidence, incidence]

/-- One page contributes `6` for equal questions and `-3` otherwise. -/
private theorem centeredQuestion_dot
    (x y : FourByThreeQuestion) :
    (∑ question : FourByThreeQuestion,
      ((3 : ℚ) * (if x = question then 1 else 0) - 1) *
        ((3 : ℚ) * (if y = question then 1 else 0) - 1)) =
      if x = y then 6 else -3 := by
  let a : FourByThreeQuestion → ℚ :=
    fun question => if x = question then 1 else 0
  let b : FourByThreeQuestion → ℚ :=
    fun question => if y = question then 1 else 0
  have ha : ∑ question, a question = 1 := by
    calc
      (∑ question, a question) = a x := by
        apply Finset.sum_eq_single x
        · intro question _ hquestion
          simp [a, hquestion.symm]
        · simp
      _ = 1 := by simp [a]
  have hb : ∑ question, b question = 1 := by
    calc
      (∑ question, b question) = b y := by
        apply Finset.sum_eq_single y
        · intro question _ hquestion
          simp [b, hquestion.symm]
        · simp
      _ = 1 := by simp [b]
  have hab :
      ∑ question, a question * b question =
        if x = y then 1 else 0 := by
    by_cases hxy : x = y
    · subst y
      rw [if_pos rfl]
      calc
        (∑ question, a question * b question) = a x * b x := by
          apply Finset.sum_eq_single x
          · intro question _ hquestion
            simp [a, b, hquestion.symm]
          · simp
        _ = 1 := by simp [a, b]
    · rw [if_neg hxy]
      apply Finset.sum_eq_zero
      intro question _
      simp only [a, b]
      split
      · rename_i hxq
        rw [if_neg (fun hyq => hxy (hxq.trans hyq.symm))]
        simp
      · simp
  change (∑ question, (3 * a question - 1) * (3 * b question - 1)) =
    if x = y then 6 else -3
  calc
    (∑ question, (3 * a question - 1) * (3 * b question - 1)) =
        9 * (∑ question, a question * b question) -
          3 * (∑ question, a question) -
          3 * (∑ question, b question) + 3 := by
      simp_rw [show ∀ question,
          (3 * a question - 1) * (3 * b question - 1) =
            9 * (a question * b question) -
              3 * a question - 3 * b question + 1 by
        intro question
        ring]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum]
      norm_num
    _ = if x = y then 6 else -3 := by
      rw [ha, hb, hab]
      split <;> norm_num

/-- The cast Hamming distance is the sum of the four unequal-coordinate indicators. -/
private theorem cast_hammingDistance
    (x y : FourByThreeClause) :
    (hammingDistance x y : ℚ) =
      ∑ page : FourByThreePlayer,
        if x page ≠ y page then 1 else 0 := by
  unfold hammingDistance
  have hcount :
      (∑ page : FourByThreePlayer,
        if x page ≠ y page then (1 : Nat) else 0) =
        (Finset.univ.filter fun page : FourByThreePlayer =>
          x page ≠ y page).card :=
    Finset.sum_boole
      (fun page : FourByThreePlayer => x page ≠ y page)
      Finset.univ
  exact_mod_cast hcount.symm

/--
The centered Gram entry is `9 * (3 - d_H)`.  Thus, away from the diagonal,
its nonzero entries occur exactly at distances one, two, and four.
-/
theorem centeredIncidenceGram_apply
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (i j : E) :
    centeredIncidenceGram query i j =
      9 * (3 - (hammingDistance (query i) (query j) : ℚ)) := by
  classical
  rw [centeredIncidenceGram, Matrix.mul_apply]
  simp only [Fintype.sum_sum_type, centeredIncidenceFeature,
    Matrix.transpose_apply]
  rw [show (∑ _constant : Fin 3, (1 : ℚ) * 1) = 3 by norm_num]
  rw [Fintype.sum_prod_type]
  simp_rw [show ∀ page : FourByThreePlayer,
      (∑ question : FourByThreeQuestion,
        (3 * rationalIncidence query i (page, question) - 1) *
          (3 * rationalIncidence query j (page, question) - 1)) =
        if query i page = query j page then 6 else -3 by
    intro page
    simpa only [rationalIncidence_apply'] using
      centeredQuestion_dot (query i page) (query j page)]
  have hdistance :=
    cast_hammingDistance (query i) (query j)
  calc
    3 + ∑ page : FourByThreePlayer,
        (if query i page = query j page then (6 : ℚ) else -3) =
        3 + ∑ page : FourByThreePlayer,
          (6 - 9 *
            (if query i page ≠ query j page then (1 : ℚ) else 0)) := by
      apply congrArg (fun value : ℚ => 3 + value)
      apply Finset.sum_congr rfl
      intro page _
      by_cases h : query i page = query j page
      · simp [h]
      · norm_num [h]
    _ = 9 * (3 - (hammingDistance (query i) (query j) : ℚ)) := by
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← hdistance]
      norm_num
      ring

/--
The centered-feature transpose and the ordinary incidence transpose have
the same zero vectors.
-/
theorem centeredIncidenceFeature_transpose_mulVec_eq_zero_iff
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (x : E → ℚ) :
    (centeredIncidenceFeature query).transpose.mulVec x = 0 ↔
      (rationalIncidence query).transpose.mulVec x = 0 := by
  classical
  let A := rationalIncidence query
  have incidenceCoordinate
      (hA : A.transpose.mulVec x = 0)
      (page : FourByThreePlayer) (question : FourByThreeQuestion) :
      ∑ e, A e (page, question) * x e = 0 := by
    have h := congrFun hA (page, question)
    simpa [Matrix.mulVec, dotProduct, A] using h
  constructor
  · intro hFeature
    have hsum : ∑ e, x e = 0 := by
      have h := congrFun hFeature (Sum.inl (0 : Fin 3))
      simpa [Matrix.mulVec, dotProduct, centeredIncidenceFeature] using h
    funext coordinate
    obtain ⟨page, question⟩ := coordinate
    have hcentered := congrFun hFeature (Sum.inr (page, question))
    have hcenteredSum :
        ∑ e, (3 * A e (page, question) - 1) * x e = 0 := by
      simpa [Matrix.mulVec, dotProduct, centeredIncidenceFeature, A] using
        hcentered
    have hexpand :
        (∑ e, (3 * A e (page, question) - 1) * x e) =
          3 * (∑ e, A e (page, question) * x e) - ∑ e, x e := by
      simp_rw [show ∀ e,
          (3 * A e (page, question) - 1) * x e =
            3 * (A e (page, question) * x e) - x e by
        intro e
        ring]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hexpand, hsum] at hcenteredSum
    have hIncidence :
        ∑ e, A e (page, question) * x e = 0 := by
      linarith
    simpa [Matrix.mulVec, dotProduct, A] using hIncidence
  · intro hIncidence
    have hsum : ∑ e, x e = 0 := by
      calc
        (∑ e, x e) =
            ∑ e, (∑ question : FourByThreeQuestion,
              A e ((0 : FourByThreePlayer), question)) * x e := by
          apply Finset.sum_congr rfl
          intro e _
          rw [rationalIncidence_hasFourByThreeIncidenceSums query e 0]
          simp
        _ = ∑ question : FourByThreeQuestion,
            ∑ e, A e ((0 : FourByThreePlayer), question) * x e := by
          simp_rw [Finset.sum_mul]
          rw [Finset.sum_comm]
        _ = 0 := by
          apply Finset.sum_eq_zero
          intro question _
          exact incidenceCoordinate hIncidence 0 question
    funext column
    cases column with
    | inl constant =>
        simpa [Matrix.mulVec, dotProduct, centeredIncidenceFeature] using hsum
    | inr coordinate =>
        obtain ⟨page, question⟩ := coordinate
        have hIncidenceCoordinate :=
          incidenceCoordinate hIncidence page question
        have hexpand :
            (∑ e, (3 * A e (page, question) - 1) * x e) =
              3 * (∑ e, A e (page, question) * x e) - ∑ e, x e := by
          simp_rw [show ∀ e,
              (3 * A e (page, question) - 1) * x e =
                3 * (A e (page, question) * x e) - x e by
            intro e
            ring]
          rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
          centeredIncidenceFeature]
        change ∑ e, (3 * A e (page, question) - 1) * x e = 0
        rw [hexpand, hIncidenceCoordinate, hsum]
        ring

/--
The centered Gram kernel is exactly the rational incidence-transpose kernel.
-/
theorem centeredIncidenceGram_ker_eq
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :
    LinearMap.ker (centeredIncidenceGram query).mulVecLin =
      LinearMap.ker ((rationalIncidence query).transpose).mulVecLin := by
  let F := centeredIncidenceFeature query
  calc
    LinearMap.ker (centeredIncidenceGram query).mulVecLin =
        LinearMap.ker ((F.transpose).mulVecLin) := by
      rw [centeredIncidenceGram]
      simpa [F] using Matrix.ker_mulVecLin_transpose_mul_self F.transpose
    _ = LinearMap.ker ((rationalIncidence query).transpose).mulVecLin := by
      ext x
      simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
      exact centeredIncidenceFeature_transpose_mulVec_eq_zero_iff query x

/-- The off-diagonal nonzero graph of the centered-incidence Gram matrix. -/
def gramNonzeroGraph {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) : SimpleGraph E where
  Adj i j := i ≠ j ∧ centeredIncidenceGram query i j ≠ 0
  symm := by
    rintro i j ⟨hij, hnonzero⟩
    refine ⟨hij.symm, ?_⟩
    rw [centeredIncidenceGram_apply query i j] at hnonzero
    rw [centeredIncidenceGram_apply query j i, hammingDistance_comm]
    exact hnonzero
  loopless := ⟨fun i hi => hi.1 rfl⟩

noncomputable instance instDecidableRelGramNonzeroGraph
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :
    DecidableRel (gramNonzeroGraph query).Adj :=
  Classical.decRel _

/--
For distinct rows, Gram adjacency means that their clause distance is not
three, equivalently that it is one, two, or four.
-/
theorem gramNonzeroGraph_adj_iff
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) (i j : E) :
    (gramNonzeroGraph query).Adj i j ↔
      i ≠ j ∧ hammingDistance (query i) (query j) ≠ 3 := by
  rw [gramNonzeroGraph]
  constructor
  · rintro ⟨hij, hgram⟩
    refine ⟨hij, ?_⟩
    intro hdistance
    rw [centeredIncidenceGram_apply, hdistance] at hgram
    norm_num at hgram
  · rintro ⟨hij, hdistance⟩
    refine ⟨hij, ?_⟩
    rw [centeredIncidenceGram_apply]
    intro hzero
    have hcast :
        (hammingDistance (query i) (query j) : ℚ) = 3 := by
      nlinarith
    exact hdistance (by exact_mod_cast hcast)

/--
Every nonzero incidence-transpose relation of a full rational circuit has
nonzero coefficient on every row.
-/
theorem fullRationalCircuit_kernel_fullSupport
    {E : Type uE} {C : Type*}
    [Fintype E] [Fintype C]
    (A : Matrix E C ℚ)
    (hCircuit : IsFullRationalCircuit A)
    (x : E → ℚ)
    (hkernel : A.transpose.mulVec x = 0)
    (hnonzero : x ≠ 0) :
    ∀ e : E, x e ≠ 0 := by
  classical
  have hsumRows : ∑ i, x i • A.row i = 0 := by
    calc
      (∑ i, x i • A.row i) = Matrix.vecMul x A :=
        (Matrix.vecMul_eq_sum x A).symm
      _ = A.transpose.mulVec x :=
        (Matrix.mulVec_transpose A x).symm
      _ = 0 := hkernel
  intro e hezero
  have hdecomp :=
    Fintype.sum_eq_add_sum_subtype_ne
      (fun i => x i • A.row i) e
  rw [hsumRows, hezero, zero_smul, zero_add] at hdecomp
  have hsubsum :
      ∑ i : {i : E // i ≠ e}, x i.1 • A.row i.1 = 0 :=
    hdecomp.symm
  have hcoefficients :
      ∀ i : {i : E // i ≠ e}, x i.1 = 0 :=
    (Fintype.linearIndependent_iff.mp (hCircuit.2 e))
      (fun i : {i : E // i ≠ e} => x i.1) hsubsum
  apply hnonzero
  funext i
  by_cases hie : i = e
  · subst i
    exact hezero
  · exact hcoefficients ⟨i, hie⟩

/-- A full rational circuit has a nonzero, hence full-support, kernel relation. -/
theorem fullRationalCircuit_exists_fullSupport_kernel
    {E : Type uE} {C : Type*}
    [Fintype E] [Fintype C]
    (A : Matrix E C ℚ)
    (hCircuit : IsFullRationalCircuit A) :
    ∃ x : E → ℚ,
      A.transpose.mulVec x = 0 ∧
        ∀ e : E, x e ≠ 0 := by
  classical
  obtain ⟨x, hsumRows, ⟨i, hi⟩⟩ :=
    Fintype.not_linearIndependent_iff.mp hCircuit.1
  have hkernel : A.transpose.mulVec x = 0 := by
    calc
      A.transpose.mulVec x = Matrix.vecMul x A :=
        Matrix.mulVec_transpose A x
      _ = ∑ i, x i • A.row i :=
        Matrix.vecMul_eq_sum x A
      _ = 0 := hsumRows
  have hnonzero : x ≠ 0 := by
    intro hx
    exact hi (congrFun hx i)
  exact ⟨x, hkernel,
    fullRationalCircuit_kernel_fullSupport
      A hCircuit x hkernel hnonzero⟩

/--
The off-diagonal nonzero Gram graph of a full rational circuit is connected.

If it were disconnected, restricting a full-support kernel relation to one
reachable component would remain in the Gram kernel, hence in the incidence
kernel, while being nonzero and vanishing outside that component.
-/
theorem fullRationalCircuit_gramNonzeroGraph_connected
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    (gramNonzeroGraph query).Connected := by
  classical
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, inferInstance⟩
  intro u v
  by_contra huv
  obtain ⟨x, hIncidenceKernel, hfullSupport⟩ :=
    fullRationalCircuit_exists_fullSupport_kernel
      (rationalIncidence query) hCircuit
  have hGramKernel :
      (centeredIncidenceGram query).mulVec x = 0 := by
    have hmem :
        x ∈ LinearMap.ker
          ((rationalIncidence query).transpose).mulVecLin := by
      exact hIncidenceKernel
    rw [← centeredIncidenceGram_ker_eq query] at hmem
    exact hmem
  let y : E → ℚ :=
    fun i => if (gramNonzeroGraph query).Reachable u i then x i else 0
  have hyGramKernel :
      (centeredIncidenceGram query).mulVec y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    by_cases hi : (gramNonzeroGraph query).Reachable u i
    · have hsumEqual :
          (∑ j, centeredIncidenceGram query i j * y j) =
            ∑ j, centeredIncidenceGram query i j * x j := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : (gramNonzeroGraph query).Reachable u j
        · simp [y, hj]
        · have hGramZero :
              centeredIncidenceGram query i j = 0 := by
            by_contra hnonzero
            have hij : i ≠ j := by
              intro hij
              subst j
              exact hj hi
            have hadj : (gramNonzeroGraph query).Adj i j :=
              ⟨hij, hnonzero⟩
            exact hj (hi.trans hadj.reachable)
          simp [y, hj, hGramZero]
      rw [hsumEqual]
      have hrow := congrFun hGramKernel i
      simpa [Matrix.mulVec, dotProduct] using hrow
    · apply Finset.sum_eq_zero
      intro j _
      by_cases hj : (gramNonzeroGraph query).Reachable u j
      · have hGramZero :
            centeredIncidenceGram query i j = 0 := by
          by_contra hnonzero
          have hij : i ≠ j := by
            intro hij
            subst j
            exact hi hj
          have hadj : (gramNonzeroGraph query).Adj i j :=
            ⟨hij, hnonzero⟩
          exact hi (hj.trans hadj.symm.reachable)
        simp [y, hj, hGramZero]
      · simp [y, hj]
  have hyIncidenceKernel :
      (rationalIncidence query).transpose.mulVec y = 0 := by
    have hmem :
        y ∈ LinearMap.ker
          (centeredIncidenceGram query).mulVecLin := by
      exact hyGramKernel
    rw [centeredIncidenceGram_ker_eq query] at hmem
    exact hmem
  have hyu : y u = x u := by
    simp [y]
  have hyv : y v = 0 := by
    simp [y, huv]
  have hynonzero : y ≠ 0 := by
    intro hyzero
    have := congrFun hyzero u
    rw [hyu] at this
    exact hfullSupport u this
  have hyfull :=
    fullRationalCircuit_kernel_fullSupport
      (rationalIncidence query) hCircuit y hyIncidenceKernel hynonzero
  exact hyfull v hyv

/-- Map an index edge to its unordered pair of clause values. -/
noncomputable def gramClauseEdgePairs
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause) :
    Finset (Finset FourByThreeClause) := by
  classical
  exact (gramNonzeroGraph query).edgeFinset.image fun edge =>
    (Sym2.map query edge).toFinset

/-- Off-diagonal symmetric pairs are determined by their underlying finsets. -/
private theorem sym2_eq_of_toFinset_eq_of_not_isDiag
    {α : Type*} [DecidableEq α]
    {e₁ e₂ : Sym2 α}
    (h₁ : ¬e₁.IsDiag) (h₂ : ¬e₂.IsDiag)
    (h : e₁.toFinset = e₂.toFinset) :
    e₁ = e₂ := by
  induction e₁ using Sym2.inductionOn with
  | _ x y =>
      induction e₂ using Sym2.inductionOn with
      | _ z w =>
          rw [Sym2.mk_isDiag_iff] at h₁ h₂
          simp only [Sym2.toFinset_mk_eq] at h
          have hz : z = x ∨ z = y := by
            have hzmem : z ∈ ({x, y} : Finset α) := by
              rw [h]
              simp
            simpa [eq_comm] using hzmem
          have hw : w = x ∨ w = y := by
            have hwmem : w ∈ ({x, y} : Finset α) := by
              rw [h]
              simp
            simpa [eq_comm] using hwmem
          rcases hz with rfl | rfl <;> rcases hw with rfl | rfl
          · exact (h₂ rfl).elim
          · rfl
          · rw [Sym2.eq_iff]
            exact Or.inr ⟨rfl, rfl⟩
          · exact (h₂ rfl).elim

/-- Injective clause labels preserve the number of Gram graph edges. -/
theorem gramClauseEdgePairs_card
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query) :
    (gramClauseEdgePairs query).card =
      (gramNonzeroGraph query).edgeFinset.card := by
  classical
  rw [gramClauseEdgePairs, Finset.card_image_iff]
  intro e₁ he₁ e₂ he₂ heq
  apply Sym2.map.injective hquery
  apply sym2_eq_of_toFinset_eq_of_not_isDiag
  · induction e₁ using Sym2.inductionOn with
    | _ i j =>
        simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
        intro hq
        apply (gramNonzeroGraph query).not_isDiag_of_mem_edgeFinset he₁
        rw [Sym2.mk_isDiag_iff]
        exact hquery hq
  · induction e₂ using Sym2.inductionOn with
    | _ i j =>
        simp only [Sym2.map_mk, Sym2.mk_isDiag_iff]
        intro hq
        apply (gramNonzeroGraph query).not_isDiag_of_mem_edgeFinset he₂
        rw [Sym2.mk_isDiag_iff]
        exact hquery hq
  · exact heq

/-- Unordered clause pairs at distances one, two, or four. -/
def nonzeroGramDistancePairs
    (centers : Finset FourByThreeClause) :
    Finset (Finset FourByThreeClause) :=
  (centerPairs centers).filter fun pair =>
    HammingPairAtDistance pair 1 ∨
      HammingPairAtDistance pair 2 ∨
      HammingPairAtDistance pair 4

/-- Distance predicate for an explicitly displayed unordered pair. -/
private theorem hammingPairAtDistance_pair_iff'
    (x y : FourByThreeClause) (hxy : x ≠ y) (distance : Nat) :
    HammingPairAtDistance {x, y} distance ↔
      hammingDistance x y = distance := by
  constructor
  · rintro ⟨⟨a, b⟩, hab⟩
    simp only [Finset.mem_filter, Finset.mem_product] at hab
    obtain ⟨⟨ha, hb⟩, hab, hdistance⟩ := hab
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hdistance
    · simpa only [hammingDistance_comm] using hdistance
    · exact (hab rfl).elim
  · intro hdistance
    exact ⟨(x, y), by simp [hxy, hdistance]⟩

/-- A two-element pair cannot simultaneously have two distinct distances. -/
private theorem nonzeroDistance_pair_indicator
    (pair : Finset FourByThreeClause)
    (hpair_card : pair.card = 2) :
    (if HammingPairAtDistance pair 1 ∨
          HammingPairAtDistance pair 2 ∨
          HammingPairAtDistance pair 4 then 1 else 0) =
      (if HammingPairAtDistance pair 1 then 1 else 0) +
        (if HammingPairAtDistance pair 2 then 1 else 0) +
        (if HammingPairAtDistance pair 4 then 1 else 0) := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hpair_card
  have h12 :
      ¬(HammingPairAtDistance {x, y} 1 ∧
        HammingPairAtDistance {x, y} 2) := by
    rintro ⟨h1, h2⟩
    have hd1 := (hammingPairAtDistance_pair_iff' x y hxy 1).1 h1
    have hd2 := (hammingPairAtDistance_pair_iff' x y hxy 2).1 h2
    omega
  have h14 :
      ¬(HammingPairAtDistance {x, y} 1 ∧
        HammingPairAtDistance {x, y} 4) := by
    rintro ⟨h1, h4⟩
    have hd1 := (hammingPairAtDistance_pair_iff' x y hxy 1).1 h1
    have hd4 := (hammingPairAtDistance_pair_iff' x y hxy 4).1 h4
    omega
  have h24 :
      ¬(HammingPairAtDistance {x, y} 2 ∧
        HammingPairAtDistance {x, y} 4) := by
    rintro ⟨h2, h4⟩
    have hd2 := (hammingPairAtDistance_pair_iff' x y hxy 2).1 h2
    have hd4 := (hammingPairAtDistance_pair_iff' x y hxy 4).1 h4
    omega
  by_cases h1 : HammingPairAtDistance {x, y} 1 <;>
    by_cases h2 : HammingPairAtDistance {x, y} 2 <;>
      by_cases h4 : HammingPairAtDistance {x, y} 4 <;>
        simp_all

/-- The number of nonzero-Gram distance pairs is `n₁+n₂+n₄`. -/
theorem nonzeroGramDistancePairs_card
    (centers : Finset FourByThreeClause) :
    (nonzeroGramDistancePairs centers).card =
      hammingDistancePairCount centers 1 +
        hammingDistancePairCount centers 2 +
        hammingDistancePairCount centers 4 := by
  classical
  simp only [nonzeroGramDistancePairs, Finset.card_filter,
    hammingDistancePairCount]
  calc
    (∑ pair ∈ centerPairs centers,
        if HammingPairAtDistance pair 1 ∨
            HammingPairAtDistance pair 2 ∨
            HammingPairAtDistance pair 4 then 1 else 0) =
      ∑ pair ∈ centerPairs centers,
        ((if HammingPairAtDistance pair 1 then 1 else 0) +
          (if HammingPairAtDistance pair 2 then 1 else 0) +
          (if HammingPairAtDistance pair 4 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro pair hpair
      exact nonzeroDistance_pair_indicator pair
        (Finset.mem_powersetCard.mp hpair).2
    _ =
        (∑ pair ∈ centerPairs centers,
          if HammingPairAtDistance pair 1 then 1 else 0) +
        (∑ pair ∈ centerPairs centers,
          if HammingPairAtDistance pair 2 then 1 else 0) +
        ∑ pair ∈ centerPairs centers,
          if HammingPairAtDistance pair 4 then 1 else 0 := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/--
For injectively labelled rows, Gram graph edges are exactly the clause pairs
at Hamming distances one, two, and four.
-/
theorem gramClauseEdgePairs_eq_nonzeroGramDistancePairs
    {E : Type uE} [Fintype E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query) :
    gramClauseEdgePairs query =
      nonzeroGramDistancePairs (Finset.univ.image query) := by
  classical
  ext pair
  constructor
  · intro hpair
    rw [gramClauseEdgePairs] at hpair
    obtain ⟨edge, hedge, hedgePair⟩ :=
      Finset.mem_image.mp hpair
    induction edge using Sym2.inductionOn with
    | _ i j =>
        simp only [Sym2.map_mk, Sym2.toFinset_mk_eq] at hedgePair
        rw [← hedgePair]
        have hadj : (gramNonzeroGraph query).Adj i j :=
          (SimpleGraph.mem_edgeSet (gramNonzeroGraph query)).mp
            (SimpleGraph.mem_edgeFinset.mp hedge)
        have hij := hadj.1
        have hqij : query i ≠ query j := by
          intro hq
          exact hij (hquery hq)
        rw [nonzeroGramDistancePairs, Finset.mem_filter]
        refine ⟨?_, ?_⟩
        · rw [centerPairs, Finset.mem_powersetCard]
          constructor
          · intro clause hclause
            simp only [Finset.mem_insert, Finset.mem_singleton] at hclause
            rcases hclause with rfl | rfl <;> simp
          · simp [hqij]
        · have hnotThree :=
            (gramNonzeroGraph_adj_iff query i j).1 hadj |>.2
          have hpositive :
              1 ≤ hammingDistance (query i) (query j) := by
            exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
              hqij ((hammingDistance_eq_zero_iff (query i) (query j)).mp
                hzero)
          have hle := hammingDistance_le_four (query i) (query j)
          have hcases :
              hammingDistance (query i) (query j) = 1 ∨
                hammingDistance (query i) (query j) = 2 ∨
                hammingDistance (query i) (query j) = 4 := by
            omega
          rcases hcases with hdistance | hdistance | hdistance
          · exact Or.inl
              ((hammingPairAtDistance_pair_iff'
                (query i) (query j) hqij 1).2 hdistance)
          · exact Or.inr (Or.inl
              ((hammingPairAtDistance_pair_iff'
                (query i) (query j) hqij 2).2 hdistance))
          · exact Or.inr (Or.inr
              ((hammingPairAtDistance_pair_iff'
                (query i) (query j) hqij 4).2 hdistance))
  · intro hpair
    rw [nonzeroGramDistancePairs, Finset.mem_filter] at hpair
    obtain ⟨hcenterPair, hdistancePair⟩ := hpair
    have hpairCard :=
      (Finset.mem_powersetCard.mp hcenterPair).2
    have hpairSubset :=
      (Finset.mem_powersetCard.mp hcenterPair).1
    obtain ⟨x, y, hxy, rfl⟩ :=
      Finset.card_eq_two.mp hpairCard
    have hxCenter := hpairSubset (by simp : x ∈ ({x, y} : Finset _))
    have hyCenter := hpairSubset (by simp : y ∈ ({x, y} : Finset _))
    obtain ⟨i, _, hix⟩ := Finset.mem_image.mp hxCenter
    obtain ⟨j, _, hjy⟩ := Finset.mem_image.mp hyCenter
    subst x
    subst y
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hxy rfl
    have hnotThree :
        hammingDistance (query i) (query j) ≠ 3 := by
      rcases hdistancePair with hdistance | hdistance | hdistance
      · have hdistance' :=
          (hammingPairAtDistance_pair_iff'
            (query i) (query j) (hquery.ne hij) 1).1 hdistance
        omega
      · have hdistance' :=
          (hammingPairAtDistance_pair_iff'
            (query i) (query j) (hquery.ne hij) 2).1 hdistance
        omega
      · have hdistance' :=
          (hammingPairAtDistance_pair_iff'
            (query i) (query j) (hquery.ne hij) 4).1 hdistance
        omega
    have hadj : (gramNonzeroGraph query).Adj i j :=
      (gramNonzeroGraph_adj_iff query i j).2 ⟨hij, hnotThree⟩
    have hedge :
        s(i, j) ∈ (gramNonzeroGraph query).edgeFinset :=
      SimpleGraph.mem_edgeFinset.mpr
        ((SimpleGraph.mem_edgeSet (gramNonzeroGraph query)).mpr hadj)
    rw [gramClauseEdgePairs]
    apply Finset.mem_image.mpr
    exact ⟨s(i, j), hedge, by simp [Sym2.toFinset_mk_eq]⟩

/--
A full rational circuit with ten rows has at least nine off-diagonal nonzero
Gram entries, counted as unordered edges.
-/
theorem tenRow_fullRationalCircuit_gramNonzeroEdgeCount_ge_nine
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hcard : Fintype.card E = 10)
    (hCircuit : IsFullRationalCircuit (rationalIncidence query)) :
    9 ≤ (gramNonzeroGraph query).edgeFinset.card := by
  classical
  have hconnected :=
    fullRationalCircuit_gramNonzeroGraph_connected query hCircuit
  have hedgeBound :=
    hconnected.card_vert_le_card_edgeSet_add_one
  have hvertexCard : Nat.card E = 10 := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hedgeCard :
      Nat.card (gramNonzeroGraph query).edgeSet =
        (gramNonzeroGraph query).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
  omega

/--
Ten distinct clauses whose radius-one balls cover all clauses cannot be the
row set of a full rational circuit.

This is the end-to-end structural obstruction: a full circuit gives a
full-support kernel vector, hence a connected nonzero Gram graph and at
least nine edges; the ten-ball cover permits at most six such clause pairs.
-/
theorem tenBallCover_not_fullRationalCircuit
    {E : Type uE} [Fintype E] [Nonempty E]
    (query : E → FourByThreeClause)
    (hquery : Function.Injective query)
    (hcard : Fintype.card E = 10)
    (hcover : RadiusOneBallCover (Finset.univ.image query)) :
    ¬IsFullRationalCircuit (rationalIncidence query) := by
  intro hCircuit
  have hcentersCard :
      (Finset.univ.image query).card = 10 := by
    rw [Finset.card_image_of_injective Finset.univ hquery,
      Finset.card_univ]
    exact hcard
  have hedgeLower :=
    tenRow_fullRationalCircuit_gramNonzeroEdgeCount_ge_nine
      query hcard hCircuit
  have hdistancePairLower :
      9 ≤
        hammingDistancePairCount (Finset.univ.image query) 1 +
          hammingDistancePairCount (Finset.univ.image query) 2 +
          hammingDistancePairCount (Finset.univ.image query) 4 := by
    calc
      9 ≤ (gramNonzeroGraph query).edgeFinset.card := hedgeLower
      _ = (gramClauseEdgePairs query).card :=
        (gramClauseEdgePairs_card query hquery).symm
      _ = (nonzeroGramDistancePairs (Finset.univ.image query)).card := by
        rw [gramClauseEdgePairs_eq_nonzeroGramDistancePairs query hquery]
      _ =
          hammingDistancePairCount (Finset.univ.image query) 1 +
            hammingDistancePairCount (Finset.univ.image query) 2 +
            hammingDistancePairCount (Finset.univ.image query) 4 :=
        nonzeroGramDistancePairs_card (Finset.univ.image query)
  exact tenBallCover_structural_contradiction
    (Finset.univ.image query) hcentersCard hcover hdistancePairLower

end

end XORGame
end QIT

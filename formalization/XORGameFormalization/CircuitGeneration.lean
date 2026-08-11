/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Lift
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Integral generation by primitive circuits

This module proves the lattice-theoretic reduction behind the structural
analysis of finite XOR supports.  For an additive homomorphism from a finite
free integer lattice to another free integer lattice, every kernel vector is
an integral combination of primitive, support-minimal nonzero kernel vectors.

The proof is elementary.  A nonzero relation contains a support-minimal
subrelation; dividing that subrelation by the gcd of its coordinates stays
in the kernel because the codomain is torsion-free.  Bézout coefficients of
the resulting primitive circuit then reduce the support of the original
relation one coordinate at a time.

The incidence-matrix interpretation is from
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:835-900].
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uE uC uP uQ

noncomputable section

/-- The finite set of coordinates on which an integer vector is nonzero. -/
def integerSupport {E : Type uE} [Fintype E]
    (y : E → ℤ) : Finset E :=
  Finset.univ.filter fun e => y e ≠ 0

@[simp]
theorem mem_integerSupport {E : Type uE} [Fintype E]
    {y : E → ℤ} {e : E} :
    e ∈ integerSupport y ↔ y e ≠ 0 := by
  simp [integerSupport]

/-- The normalized gcd (content) of the coordinates of an integer vector. -/
def integerContent {E : Type uE} [Fintype E]
    (y : E → ℤ) : ℤ :=
  Finset.univ.gcd y

/-- An integer vector is primitive when its coordinate gcd is one. -/
def IsPrimitiveIntegerVector {E : Type uE} [Fintype E]
    (y : E → ℤ) : Prop :=
  integerContent y = 1

/--
A nonzero kernel vector is support-minimal when every nonzero kernel vector
supported inside it has exactly the same support.
-/
def IsSupportMinimalKernelVector {E : Type uE} {C : Type uC}
    [Fintype E] (φ : (E → ℤ) →+ (C → ℤ)) (y : E → ℤ) : Prop :=
  φ y = 0 ∧ y ≠ 0 ∧
    ∀ z : E → ℤ,
      φ z = 0 →
      z ≠ 0 →
      integerSupport z ⊆ integerSupport y →
      integerSupport y ⊆ integerSupport z

/--
A primitive integer circuit is a primitive, nonzero, support-minimal vector
in the integer kernel.
-/
def IsPrimitiveKernelCircuit {E : Type uE} {C : Type uC}
    [Fintype E] (φ : (E → ℤ) →+ (C → ℤ)) (y : E → ℤ) : Prop :=
  IsSupportMinimalKernelVector φ y ∧ IsPrimitiveIntegerVector y

/-- The set of primitive integer circuits of an additive homomorphism. -/
def primitiveKernelCircuits {E : Type uE} {C : Type uC}
    [Fintype E] (φ : (E → ℤ) →+ (C → ℤ)) : Set (E → ℤ) :=
  {y | IsPrimitiveKernelCircuit φ y}

/-- A vector is zero exactly when its integer support is empty. -/
theorem integerSupport_eq_empty_iff {E : Type uE} [Fintype E]
    (y : E → ℤ) :
    integerSupport y = ∅ ↔ y = 0 := by
  constructor
  · intro h
    funext e
    by_contra he
    have : e ∈ integerSupport y := mem_integerSupport.mpr he
    simp [h] at this
  · rintro rfl
    simp [integerSupport]

/-- A nonzero vector has nonzero integer content. -/
theorem integerContent_ne_zero_of_ne_zero {E : Type uE} [Fintype E]
    {y : E → ℤ} (hy : y ≠ 0) :
    integerContent y ≠ 0 := by
  intro hcontent
  apply hy
  funext e
  exact
    (Finset.gcd_eq_zero_iff.mp hcontent e (Finset.mem_univ e))

/-- Divide every coordinate by the vector's integer content. -/
def primitivePart {E : Type uE} [Fintype E]
    (y : E → ℤ) : E → ℤ :=
  fun e => y e / integerContent y

/-- Multiplying the primitive part by the content recovers each coordinate. -/
theorem integerContent_mul_primitivePart {E : Type uE} [Fintype E]
    (y : E → ℤ) (e : E) :
    integerContent y * primitivePart y e = y e := by
  rw [mul_comm]
  exact Int.ediv_mul_cancel (Finset.gcd_dvd (Finset.mem_univ e))

/-- Dividing a nonzero vector by its content does not change its support. -/
theorem integerSupport_primitivePart {E : Type uE} [Fintype E]
    {y : E → ℤ} (hy : y ≠ 0) :
    integerSupport (primitivePart y) = integerSupport y := by
  ext e
  simp only [mem_integerSupport]
  have hcontent := integerContent_ne_zero_of_ne_zero hy
  constructor
  · intro hpart hzero
    have hproduct := integerContent_mul_primitivePart y e
    rw [hzero] at hproduct
    exact hpart ((mul_eq_zero.mp hproduct).resolve_left hcontent)
  · intro hyCoord hpart
    have hproduct := integerContent_mul_primitivePart y e
    rw [hpart, mul_zero] at hproduct
    exact hyCoord hproduct.symm

/-- The primitive part of a nonzero integer vector has coordinate gcd one. -/
theorem primitivePart_isPrimitive {E : Type uE} [Fintype E]
    {y : E → ℤ} (hy : y ≠ 0) :
    IsPrimitiveIntegerVector (primitivePart y) := by
  have hexists : ∃ e : E, y e ≠ 0 := by
    by_contra h
    push Not at h
    apply hy
    funext e
    exact h e
  obtain ⟨e, he⟩ := hexists
  exact Finset.gcd_div_eq_one (Finset.mem_univ e) he

/--
For a homomorphism into an integer function lattice, dividing a nonzero
kernel vector by its content remains in the kernel.
-/
theorem primitivePart_mem_ker {E : Type uE} {C : Type uC}
    [Fintype E] (φ : (E → ℤ) →+ (C → ℤ))
    {y : E → ℤ} (hyker : φ y = 0) (hy : y ≠ 0) :
    φ (primitivePart y) = 0 := by
  have hscale : integerContent y • primitivePart y = y := by
    funext e
    simp only [Pi.smul_apply, zsmul_eq_mul]
    exact integerContent_mul_primitivePart y e
  have hmapped : integerContent y • φ (primitivePart y) = 0 := by
    rw [← φ.map_zsmul, hscale, hyker]
  funext c
  have hc := congrFun hmapped c
  simp only [Pi.smul_apply, zsmul_eq_mul, Pi.zero_apply] at hc
  exact (mul_eq_zero.mp hc).resolve_left
    (integerContent_ne_zero_of_ne_zero hy)

/--
Every nonzero kernel vector contains, in its support, a primitive integer
circuit.  Finiteness is used only to choose a relation of minimum support.
-/
theorem exists_primitiveKernelCircuit_support_subset
    {E : Type uE} {C : Type uC} [Fintype E]
    (φ : (E → ℤ) →+ (C → ℤ))
    {y : E → ℤ} (hyker : φ y = 0) (hy : y ≠ 0) :
    ∃ c : E → ℤ,
      IsPrimitiveKernelCircuit φ c ∧
        integerSupport c ⊆ integerSupport y := by
  classical
  let P : ℕ → Prop := fun n =>
    ∃ z : E → ℤ,
      φ z = 0 ∧ z ≠ 0 ∧
        integerSupport z ⊆ integerSupport y ∧
          (integerSupport z).card = n
  have hP : ∃ n, P n :=
    ⟨(integerSupport y).card, y, hyker, hy, fun _ h => h, rfl⟩
  obtain ⟨z, hzker, hz, hzy, hzcard⟩ := Nat.find_spec hP
  let c : E → ℤ := primitivePart z
  have hcsupport : integerSupport c = integerSupport z := by
    exact integerSupport_primitivePart hz
  have hcker : φ c = 0 := primitivePart_mem_ker φ hzker hz
  have hcprimitive : IsPrimitiveIntegerVector c :=
    primitivePart_isPrimitive hz
  have hc : c ≠ 0 := by
    intro hc
    have : integerSupport z = ∅ := by
      rw [← hcsupport, hc]
      simp [integerSupport]
    exact hz ((integerSupport_eq_empty_iff z).mp this)
  refine ⟨c, ⟨⟨hcker, hc, ?_⟩, hcprimitive⟩, ?_⟩
  · intro w hwker hw hwc
    have hwz : integerSupport w ⊆ integerSupport z := by
      simpa [hcsupport] using hwc
    have hwy : integerSupport w ⊆ integerSupport y :=
      fun e he => hzy (hwz he)
    have hwP : P (integerSupport w).card :=
      ⟨w, hwker, hw, hwy, rfl⟩
    have hmin : Nat.find hP ≤ (integerSupport w).card :=
      Nat.find_min' hP hwP
    have hcardZW : (integerSupport z).card ≤
        (integerSupport w).card := by
      simpa [hzcard] using hmin
    have heq : integerSupport w = integerSupport z :=
      Finset.eq_of_subset_of_card_le hwz hcardZW
    simp [hcsupport, heq]
  · simpa [hcsupport] using hzy

/--
The integer kernel is contained in the additive subgroup generated by its
primitive circuits.

This is the integral circuit-generation theorem.  No Cramer, exterior-power,
unimodularity, or finite-enumeration hypothesis is needed.
-/
theorem integerKernel_le_closure_primitiveCircuits
    {E : Type uE} {C : Type uC} [Fintype E]
    (φ : (E → ℤ) →+ (C → ℤ)) :
    φ.ker ≤ AddSubgroup.closure (primitiveKernelCircuits φ) := by
  classical
  let H : AddSubgroup (E → ℤ) :=
    AddSubgroup.closure (primitiveKernelCircuits φ)
  have hgenerate :
      ∀ n : ℕ, ∀ y : E → ℤ,
        φ y = 0 →
        (integerSupport y).card = n →
        y ∈ H := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro y hyker hycard
        by_cases hy : y = 0
        · subst y
          exact H.zero_mem
        obtain ⟨c, hc, hcy⟩ :=
          exists_primitiveKernelCircuit_support_subset φ hyker hy
        have hcH : c ∈ H :=
          AddSubgroup.subset_closure hc
        have hmultiple : ∀ e : E, c e • y ∈ H := by
          intro e
          by_cases hce : c e = 0
          · simp [hce]
          let w : E → ℤ := c e • y - y e • c
          have hwker : φ w = 0 := by
            dsimp [w]
            rw [φ.map_sub, φ.map_zsmul, φ.map_zsmul, hyker, hc.1.1]
            simp
          have hwsubset :
              integerSupport w ⊆ integerSupport y := by
            intro j hj
            have hwj : w j ≠ 0 := mem_integerSupport.mp hj
            have hyj : y j ≠ 0 := by
              intro hyj
              have hcj : c j = 0 := by
                by_contra hcj
                have hjc : j ∈ integerSupport c :=
                  mem_integerSupport.mpr hcj
                exact (mem_integerSupport.mp (hcy hjc)) hyj
              apply hwj
              simp [w, hyj, hcj]
            exact mem_integerSupport.mpr hyj
          have hey : e ∈ integerSupport y :=
            hcy (mem_integerSupport.mpr hce)
          have hew : e ∉ integerSupport w := by
            simp [integerSupport, w, zsmul_eq_mul, mul_comm]
          have hwproper :
              integerSupport w ⊂ integerSupport y := by
            rw [Finset.ssubset_iff_subset_ne]
            refine ⟨hwsubset, ?_⟩
            intro heq
            exact hew (heq ▸ hey)
          have hwcard :
              (integerSupport w).card < n := by
            rw [← hycard]
            exact Finset.card_lt_card hwproper
          have hwH : w ∈ H :=
            ih (integerSupport w).card hwcard w hwker rfl
          have hye : y e • c ∈ H :=
            H.zsmul_mem hcH (y e)
          have hdecomp : c e • y = w + y e • c := by
            dsimp [w]
            abel
          rw [hdecomp]
          exact H.add_mem hwH hye
        obtain ⟨a, ha⟩ :=
          Finset.gcd_eq_sum_mul Finset.univ c
        have hcContent : integerContent c = 1 := hc.2
        have hcoeff :
            ∑ e ∈ Finset.univ, c e * a e = (1 : ℤ) := by
          calc
            ∑ e ∈ Finset.univ, c e * a e = integerContent c := by
              simpa [integerContent] using ha.symm
            _ = 1 := hcContent
        have hsum :
            (∑ e ∈ Finset.univ, (c e * a e) • y) ∈ H := by
          apply sum_mem
          intro e _
          have := H.zsmul_mem (hmultiple e) (a e)
          simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc] using this
        have hsum_eq :
            ∑ e ∈ Finset.univ, (c e * a e) • y = y := by
          rw [← Finset.sum_smul, hcoeff]
          simp
        rwa [hsum_eq] at hsum
  intro y hy
  change φ y = 0 at hy
  exact hgenerate (integerSupport y).card y hy rfl

/-- The primitive circuits generate exactly the integer kernel. -/
theorem primitiveCircuits_closure_eq_kernel
    {E : Type uE} {C : Type uC} [Fintype E]
    (φ : (E → ℤ) →+ (C → ℤ)) :
    AddSubgroup.closure (primitiveKernelCircuits φ) = φ.ker := by
  apply le_antisymm
  · apply (AddSubgroup.closure_le φ.ker).mpr
    intro c hc
    exact hc.1.1
  · exact integerKernel_le_closure_primitiveCircuits φ

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- The additive homomorphism represented by the transposed incidence matrix. -/
def incidenceRelationHom [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) :
    (ClauseId → ℤ) →+ (Player × Question → ℤ) where
  toFun y pq :=
    ∑ clause : ClauseId, incidence query clause pq * y clause
  map_zero' := by
    funext pq
    simp
  map_add' left right := by
    funext pq
    simp [mul_add, Finset.sum_add_distrib]

@[simp]
theorem incidenceRelationHom_apply
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (y : ClauseId → ℤ) (pq : Player × Question) :
    incidenceRelationHom query y pq =
      ∑ clause : ClauseId, incidence query clause pq * y clause := rfl

/-- Incidence relations are exactly elements of the incidence homomorphism's kernel. -/
theorem isIntegerRelation_iff_mem_incidenceRelationHom_ker
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (y : ClauseId → ℤ) :
    IsIntegerRelation query y ↔ y ∈ (incidenceRelationHom query).ker := by
  constructor
  · intro hy
    change incidenceRelationHom query y = 0
    funext pq
    exact hy pq
  · intro hy pq
    change incidenceRelationHom query y = 0 at hy
    exact congrFun hy pq

/--
If every primitive incidence circuit admits a balanced lift, then every
integer incidence relation admits one.  This is the downstream bridge from
integral circuit generation to equality of the two XOR parity spaces.
-/
theorem everyIntegerRelationHasBalancedLift_of_primitiveCircuits
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (hlift :
      ∀ c : ClauseId → ℤ,
        IsPrimitiveKernelCircuit (incidenceRelationHom query) c →
          HasBalancedLift query c) :
    EveryIntegerRelationHasBalancedLift query := by
  intro y hy
  apply hasBalancedLift_of_mem_addSubgroup_closure
    query (primitiveKernelCircuits (incidenceRelationHom query))
  · intro c hc
    exact hlift c hc
  · exact integerKernel_le_closure_primitiveCircuits
      (incidenceRelationHom query)
      ((isIntegerRelation_iff_mem_incidenceRelationHom_ker query y).mp hy)

end

end XORGame
end QIT

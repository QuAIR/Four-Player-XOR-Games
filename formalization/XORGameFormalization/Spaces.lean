/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Refutation
public import XORGameFormalization.Parity

/-!
# Integer-relation and refutation parity spaces

For a fixed unsigned XOR support, this module packages the two binary parity
spaces used by the perfect-strategy reduction:

* integer incidence-relation parities;
* balanced operator-refutation-word parities.

The alternating-lift theorem gives the structural inclusion from refutation
parity to integer-relation parity. Equality of the spaces then turns the
combinatorial perfectness proxy for commuting strategies into the MERP
perfectness proxy.

The source-level PREF and operator-refutation notions are recorded in
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:1346-1360] and
[WattsHarrowKanwarNatarajan2018XORGames,
watts-harrow-kanwar-natarajan-2018-xor-games.tex:3232-3309].
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uP uQ uC

noncomputable section

variable {Player : Type uP} {Question : Type uQ} {ClauseId : Type uC}

/-- The binary span of parities of all integer incidence relations. -/
def integerRelationParitySpace
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) :
    ParitySpace ClauseId :=
  Submodule.span (ZMod 2)
    {parity | ∃ y : ClauseId → ℤ,
      IsIntegerRelation query y ∧ relationParity y = parity}

/-- The binary span of occurrence parities of all balanced clause words. -/
def refutationParitySpace
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) :
    ParitySpace ClauseId :=
  Submodule.span (ZMod 2)
    {parity | ∃ word : List ClauseId,
      IsBalancedWord query word ∧ occurrenceParity word = parity}

/--
An integer relation has a balanced lift when its binary parity is realized by
the occurrence parity of an exact involution-reducing clause word.
-/
def HasBalancedLift [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question) (y : ClauseId → ℤ) : Prop :=
  ∃ word : List ClauseId,
    IsBalancedWord query word ∧
      occurrenceParity word = relationParity y

/--
The support-level lifting property needed in the global XOR-game argument:
every integer incidence relation has a balanced lift with the same parity.
-/
def EveryIntegerRelationHasBalancedLift
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) : Prop :=
  ∀ y : ClauseId → ℤ,
    IsIntegerRelation query y → HasBalancedLift query y

/--
Every balanced-word parity lies in the integer-relation parity space.

This is the subspace form of `operatorRefutation_implies_pref`; it does not
use clause signs.
-/
theorem refutationParitySpace_le_integerRelationParitySpace
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) :
    refutationParitySpace query ≤ integerRelationParitySpace query := by
  apply Submodule.span_le.2
  rintro parity ⟨word, hbalanced, rfl⟩
  apply Submodule.subset_span
  refine ⟨alternatingLift word,
    balancedWord_alternatingLift_isIntegerRelation query word hbalanced, ?_⟩
  exact alternatingLift_mod_two word

/--
If every integer relation parity has a balanced lift, the refutation and
integer-relation parity spaces coincide.
-/
theorem paritySpaces_eq_of_everyIntegerRelationHasBalancedLift
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (hlift : EveryIntegerRelationHasBalancedLift query) :
    refutationParitySpace query = integerRelationParitySpace query := by
  apply le_antisymm
  · exact refutationParitySpace_le_integerRelationParitySpace query
  · apply Submodule.span_le.2
    rintro parity ⟨y, hy, rfl⟩
    rcases hlift y hy with ⟨word, hbalanced, hparity⟩
    apply Submodule.subset_span
    exact ⟨word, hbalanced, hparity⟩

/--
Under the support-level lifting property, every PREF witness can be converted
to a true operator refutation.
-/
theorem hasOperatorRefutation_of_pref_of_everyIntegerRelationHasBalancedLift
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2)
    (hlift : EveryIntegerRelationHasBalancedLift query) :
    HasPREF query sign → HasOperatorRefutation query sign := by
  rintro ⟨y, hy, hodd⟩
  rcases hlift y hy with ⟨word, hbalanced, hparity⟩
  refine ⟨word, hbalanced, ?_⟩
  rw [hparity]
  exact hodd

/-- The dot-product functional associated with a binary clause-sign vector. -/
def parityFunctional [Fintype ClauseId]
    (sign : ClauseId → ZMod 2) :
    Module.Dual (ZMod 2) (ClauseId → ZMod 2) where
  toFun parity := parityPairing sign parity
  map_add' left right := by
    simp [parityPairing, mul_add, Finset.sum_add_distrib]
  map_smul' scalar parity := by
    simp [parityPairing, Finset.mul_sum, mul_left_comm]

/--
The parity-space proxy for MERP perfection: the sign functional annihilates
every integer-relation parity.
-/
def IsMERPPerfectParity
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) : Prop :=
  parityFunctional sign ∈
    (integerRelationParitySpace query).dualAnnihilator

/--
The parity-space proxy for commuting perfection: the sign functional
annihilates every balanced-word parity.
-/
def IsCommutingPerfectParity
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) : Prop :=
  parityFunctional sign ∈
    (refutationParitySpace query).dualAnnihilator

private theorem mem_span_dualAnnihilator_iff
    {generators : Set (ClauseId → ZMod 2)}
    (φ : Module.Dual (ZMod 2) (ClauseId → ZMod 2)) :
    φ ∈ (Submodule.span (ZMod 2) generators).dualAnnihilator ↔
      ∀ parity ∈ generators, φ parity = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro hann parity hparity
    exact hann parity (Submodule.subset_span hparity)
  · intro hzero parity hparity
    have hle :
        Submodule.span (ZMod 2) generators ≤ LinearMap.ker φ :=
      Submodule.span_le.2 fun generator hgenerator =>
        hzero generator hgenerator
    exact hle hparity

private theorem zmodTwo_eq_zero_or_one (x : ZMod 2) :
    x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
The parity-space MERP condition is exactly the absence of an integer PREF.
-/
theorem isMERPPerfectParity_iff_not_hasPREF
    [Fintype ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) :
    IsMERPPerfectParity query sign ↔ ¬ HasPREF query sign := by
  rw [IsMERPPerfectParity, integerRelationParitySpace,
    mem_span_dualAnnihilator_iff]
  constructor
  · intro hann ⟨y, hy, hodd⟩
    have hzero :=
      hann (relationParity y) ⟨y, hy, rfl⟩
    change parityPairing sign (relationParity y) = 0 at hzero
    rw [hodd] at hzero
    exact one_ne_zero hzero
  · intro hnopref parity
    rintro ⟨y, hy, rfl⟩
    change parityPairing sign (relationParity y) = 0
    rcases zmodTwo_eq_zero_or_one
        (parityPairing sign (relationParity y)) with hzero | hone
    · exact hzero
    · exact False.elim (hnopref ⟨y, hy, hone⟩)

/--
The parity-space commuting condition is exactly the absence of a balanced
operator-refutation word.
-/
theorem isCommutingPerfectParity_iff_not_hasOperatorRefutation
    [Fintype ClauseId] [DecidableEq ClauseId]
    (query : ClauseId → Clause Player Question)
    (sign : ClauseId → ZMod 2) :
    IsCommutingPerfectParity query sign ↔
      ¬ HasOperatorRefutation query sign := by
  rw [IsCommutingPerfectParity, refutationParitySpace,
    mem_span_dualAnnihilator_iff]
  constructor
  · intro hann ⟨word, hbalanced, hodd⟩
    have hzero :=
      hann (occurrenceParity word) ⟨word, hbalanced, rfl⟩
    change parityPairing sign (occurrenceParity word) = 0 at hzero
    rw [hodd] at hzero
    exact one_ne_zero hzero
  · intro hnorefutation parity
    rintro ⟨word, hbalanced, rfl⟩
    change parityPairing sign (occurrenceParity word) = 0
    rcases zmodTwo_eq_zero_or_one
        (parityPairing sign (occurrenceParity word)) with hzero | hone
    · exact hzero
    · exact False.elim (hnorefutation ⟨word, hbalanced, hone⟩)

/--
If the two support parity spaces coincide, commuting-perfect parity implies
MERP-perfect parity for every sign vector.

The analytic identifications of these two proxies with actual perfect
strategies are deliberately kept outside this purely combinatorial theorem.
-/
theorem commutingPerfectParity_implies_merpPerfectParity_of_spaces_eq
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question)
    (hspaces :
      refutationParitySpace query = integerRelationParitySpace query)
    (sign : ClauseId → ZMod 2)
    (hperfect : IsCommutingPerfectParity query sign) :
    IsMERPPerfectParity query sign := by
  simpa [IsCommutingPerfectParity, IsMERPPerfectParity, hspaces] using hperfect

/--
Exact abstract support-gap criterion: because refutation parity is always
contained in relation parity, equality is equivalent to the reverse
containment of their dual annihilators.
-/
theorem refutationParitySpace_eq_integerRelationParitySpace_iff
    [Fintype ClauseId] [DecidableEq ClauseId] [DecidableEq Question]
    (query : ClauseId → Clause Player Question) :
    refutationParitySpace query = integerRelationParitySpace query ↔
      (refutationParitySpace query).dualAnnihilator ≤
        (integerRelationParitySpace query).dualAnnihilator :=
  paritySpace_eq_iff_dualAnnihilator_le_of_le
    (refutationParitySpace_le_integerRelationParitySpace query)

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.Basic
public import XORGameFormalization.Hamming
public meta import XORGameFormalization.Hamming
public meta import Mathlib.Data.Fintype.Pi
public meta import Mathlib.Data.Fintype.Prod

/-!
# A ternary perfect code for four-player clauses

The map

`(a, b) ↦ (a, b, a + b, a + 2b)`

defines a nine-word ternary code in the 81-element space of four-player,
three-question clauses.  Its nine additive cosets partition the clause
space.  Every radius-one Hamming ball contains exactly one word from each
coset.

The closed finite calculations below concern only this fixed code.  They do
not enumerate XOR-game circuit supports.
-/

@[expose] public section

namespace QIT
namespace XORGame

/-- A message for the two-dimensional ternary code. -/
abbrev TernaryMessage := Fin 3 × Fin 3

/-- An index for one of the nine additive cosets of the ternary code. -/
abbrev TernarySyndrome := Fin 3 × Fin 3

/-- There are exactly nine ternary syndrome indices. -/
@[simp]
theorem ternarySyndrome_card :
    Fintype.card TernarySyndrome = 9 := by
  native_decide

/--
The codeword `(a, b, a + b, a + 2b)` associated to a ternary message.

Arithmetic in `Fin 3` is arithmetic modulo three.
-/
def ternaryCodeword (message : TernaryMessage) : FourByThreeClause :=
  fun
    | 0 => message.1
    | 1 => message.2
    | 2 => message.1 + message.2
    | 3 => message.1 + message.2 + message.2

/-- The ternary code consists of the nine encoded messages. -/
def ternaryCode : Finset FourByThreeClause :=
  Finset.univ.image ternaryCodeword

/-- The ternary encoding is injective. -/
theorem ternaryCodeword_injective :
    Function.Injective ternaryCodeword := by
  intro x y hxy
  apply Prod.ext
  · exact congrFun hxy 0
  · exact congrFun hxy 1

/-- The ternary code contains exactly nine words. -/
@[simp]
theorem ternaryCode_card :
    ternaryCode.card = 9 := by
  native_decide

/-- Distinct codewords have Hamming distance exactly three. -/
theorem hammingDistance_ternaryCodeword
    (x y : TernaryMessage) (hxy : x ≠ y) :
    hammingDistance (ternaryCodeword x) (ternaryCodeword y) = 3 := by
  exact (by
    native_decide :
      ∀ x y : TernaryMessage, x ≠ y →
        hammingDistance (ternaryCodeword x) (ternaryCodeword y) = 3) x y hxy

/-- Pointwise addition of two four-player ternary clauses. -/
def addTernaryClauses
    (x y : FourByThreeClause) : FourByThreeClause :=
  fun coordinate => x coordinate + y coordinate

/--
The canonical representative `(0, 0, u, v)` of the coset indexed by
the syndrome `(u, v)`.
-/
def ternarySyndromeRepresentative
    (syndrome : TernarySyndrome) : FourByThreeClause :=
  fun
    | 0 => 0
    | 1 => 0
    | 2 => syndrome.1
    | 3 => syndrome.2

/-- A word in the coset indexed by `syndrome`. -/
def ternaryCosetWord
    (syndrome : TernarySyndrome) (message : TernaryMessage) :
    FourByThreeClause :=
  addTernaryClauses
    (ternaryCodeword message)
    (ternarySyndromeRepresentative syndrome)

/-- The additive coset indexed by `syndrome`. -/
def ternaryCoset
    (syndrome : TernarySyndrome) : Finset FourByThreeClause :=
  Finset.univ.image (ternaryCosetWord syndrome)

/-- Every additive coset of the ternary code contains nine words. -/
@[simp]
theorem ternaryCoset_card (syndrome : TernarySyndrome) :
    (ternaryCoset syndrome).card = 9 := by
  exact (by
    native_decide :
      ∀ syndrome : TernarySyndrome,
        (ternaryCoset syndrome).card = 9) syndrome

/--
The two parity checks that label the nine cosets.

For a clause `x`, the syndrome is
`(x₂ - x₀ - x₁, x₃ - x₀ - 2x₁)`.
-/
def ternarySyndromeOf
    (x : FourByThreeClause) : TernarySyndrome :=
  (x 2 - x 0 - x 1, x 3 - x 0 - x 1 - x 1)

/-- Coset membership is exactly equality of syndromes. -/
theorem mem_ternaryCoset_iff_syndrome
    (x : FourByThreeClause) (syndrome : TernarySyndrome) :
    x ∈ ternaryCoset syndrome ↔ ternarySyndromeOf x = syndrome := by
  exact (by
    native_decide :
      ∀ x : FourByThreeClause, ∀ syndrome : TernarySyndrome,
        x ∈ ternaryCoset syndrome ↔ ternarySyndromeOf x = syndrome) x syndrome

/-- Every four-player ternary clause belongs to exactly one code coset. -/
theorem existsUnique_mem_ternaryCoset
    (x : FourByThreeClause) :
    ∃! syndrome : TernarySyndrome, x ∈ ternaryCoset syndrome := by
  refine ⟨ternarySyndromeOf x, ?_, ?_⟩
  · exact (mem_ternaryCoset_iff_syndrome x (ternarySyndromeOf x)).2 rfl
  · intro syndrome hmem
    exact ((mem_ternaryCoset_iff_syndrome x syndrome).1 hmem).symm

/-- Distinct syndrome indices give disjoint code cosets. -/
theorem ternaryCoset_disjoint
    (s t : TernarySyndrome) (hst : s ≠ t) :
    Disjoint (ternaryCoset s) (ternaryCoset t) := by
  refine Finset.disjoint_left.mpr ?_
  intro x hxs hxt
  apply hst
  exact ((mem_ternaryCoset_iff_syndrome x s).1 hxs).symm.trans
    ((mem_ternaryCoset_iff_syndrome x t).1 hxt)

/-- The nine ternary-code cosets cover all 81 four-player clauses. -/
theorem ternaryCosets_biUnion :
    Finset.univ.biUnion ternaryCoset =
      (Finset.univ : Finset FourByThreeClause) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · intro
    trivial
  · intro
    exact (existsUnique_mem_ternaryCoset x).exists

/--
Every radius-one Hamming ball contains exactly one word from each of the
nine ternary-code cosets.
-/
theorem radiusOneBall_inter_ternaryCoset_card
    (center : FourByThreeClause) (syndrome : TernarySyndrome) :
    (radiusOneBall center ∩ ternaryCoset syndrome).card = 1 := by
  exact (by
    native_decide :
      ∀ center : FourByThreeClause, ∀ syndrome : TernarySyndrome,
        (radiusOneBall center ∩ ternaryCoset syndrome).card = 1) center syndrome

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import XORGameFormalization.SafeCenter

/-!
# Packing safe centers in the even Hamming layers

For any nonempty support, safety and even support distance place every safe
center in layer two or four about one fixed support clause.  If the safe
centers are mutually distance at least three, the universal four-coordinate
packing bound therefore limits them to six.
-/

@[expose] public section

namespace QIT
namespace XORGame

noncomputable section

/--
Safety, parity, and the four-coordinate diameter put a support clause in
exactly layer two or layer four about a safe center.
-/
theorem safeCenter_support_distance_two_or_four
    (support : Finset FourByThreeClause)
    (center clause : FourByThreeClause)
    (hcenter : center ∈ safeCenters support)
    (hclause : clause ∈ support)
    (heven : Even (hammingDistance center clause)) :
    hammingDistance center clause = 2 ∨
      hammingDistance center clause = 4 := by
  have hlower :
      2 ≤ hammingDistance center clause :=
    (Finset.mem_filter.mp hcenter).2 clause hclause
  have hupper :
      hammingDistance center clause ≤ 4 :=
    hammingDistance_le_four center clause
  obtain ⟨half, hhalf⟩ := heven
  omega

/--
A nonempty support with even, pairwise-separated safe centers has at most
six safe centers.
-/
theorem safeCenters_card_le_six_of_even_separated
    (support : Finset FourByThreeClause)
    (hsupport : support.Nonempty)
    (hseparated :
      ∀ ⦃u⦄, u ∈ safeCenters support →
        ∀ ⦃v⦄, v ∈ safeCenters support →
          u ≠ v → 3 ≤ hammingDistance u v)
    (heven :
      ∀ center ∈ safeCenters support,
        ∀ clause ∈ support,
          Even (hammingDistance center clause)) :
    (safeCenters support).card ≤ 6 := by
  let anchor : FourByThreeClause := Classical.choose hsupport
  have hanchor : anchor ∈ support :=
    Classical.choose_spec hsupport
  apply separated_layers_two_four_card_le_six
    anchor (safeCenters support)
  · intro center hcenter
    have hlayers :
        hammingDistance center anchor = 2 ∨
          hammingDistance center anchor = 4 :=
      safeCenter_support_distance_two_or_four
        support center anchor hcenter hanchor
          (heven center hcenter anchor hanchor)
    simpa [hammingDistance_comm] using hlayers
  · exact hseparated

end

end XORGame
end QIT

/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Fintype.EquivFin

/-!
# Three-color selected-block forests

This module packages the abstract three-color occurrence-signature problem.
Positive and negative vertices carry signatures of at most two colors, and
each color is balanced between the two sides.
-/

@[expose] public section

namespace QIT
namespace XORGame

universe uC uP uN

noncomputable section

/-- A balanced collection of signatures over at most three colors. -/
structure ColorSignatureSystem
    (Color : Type uC) (Positive : Type uP) (Negative : Type uN)
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative] where
  /-- Colors incident to a positive vertex. -/
  positiveSignature : Positive → Finset Color
  /-- Colors incident to a negative vertex. -/
  negativeSignature : Negative → Finset Color
  /-- Positive signatures have size at most two. -/
  positive_card_le_two :
    ∀ positive, (positiveSignature positive).card ≤ 2
  /-- Negative signatures have size at most two. -/
  negative_card_le_two :
    ∀ negative, (negativeSignature negative).card ≤ 2
  /-- Every color has equally many endpoints on the two sides. -/
  balanced :
    ∀ color,
      (Finset.univ.filter
          (fun positive => color ∈ positiveSignature positive)).card =
        (Finset.univ.filter
          (fun negative => color ∈ negativeSignature negative)).card

namespace ColorSignatureSystem

variable
    {Color : Type uC} {Positive : Type uP} {Negative : Type uN}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]

/-- The balance field rewritten as equality of eligible endpoint types. -/
theorem eligible_card_eq
    (system : ColorSignatureSystem Color Positive Negative)
    (color : Color) :
    Fintype.card
        {positive : Positive //
          color ∈ system.positiveSignature positive} =
      Fintype.card
        {negative : Negative //
          color ∈ system.negativeSignature negative} := by
  calc
    _ =
        (Finset.univ.filter
          (fun positive =>
            color ∈ system.positiveSignature positive)).card := by
      exact Fintype.card_ofFinset _ (by
        intro positive
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl)
    _ =
        (Finset.univ.filter
          (fun negative =>
            color ∈ system.negativeSignature negative)).card :=
      system.balanced color
    _ = _ := by
      symm
      exact Fintype.card_ofFinset _ (by
        intro negative
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rfl)

/-- A positive color incidence has some negative endpoint of that color. -/
theorem exists_negative_of_positive_mem
    (system : ColorSignatureSystem Color Positive Negative)
    {color : Color} {positive : Positive}
    (hpositive : color ∈ system.positiveSignature positive) :
    ∃ negative, color ∈ system.negativeSignature negative := by
  have hpositiveNonempty :
      (Finset.univ.filter
        (fun other =>
          color ∈ system.positiveSignature other)).Nonempty :=
    ⟨positive, by simp [hpositive]⟩
  have hnegativeCard :
      0 <
        (Finset.univ.filter
          (fun negative =>
            color ∈ system.negativeSignature negative)).card := by
    rw [← system.balanced color]
    exact Finset.card_pos.mpr hpositiveNonempty
  obtain ⟨negative, hnegative⟩ :=
    Finset.card_pos.mp hnegativeCard
  exact ⟨negative, (Finset.mem_filter.mp hnegative).2⟩

/-- A negative color incidence has some positive endpoint of that color. -/
theorem exists_positive_of_negative_mem
    (system : ColorSignatureSystem Color Positive Negative)
    {color : Color} {negative : Negative}
    (hnegative : color ∈ system.negativeSignature negative) :
    ∃ positive, color ∈ system.positiveSignature positive := by
  have hnegativeNonempty :
      (Finset.univ.filter
        (fun other =>
          color ∈ system.negativeSignature other)).Nonempty :=
    ⟨negative, by simp [hnegative]⟩
  have hpositiveCard :
      0 <
        (Finset.univ.filter
          (fun positive =>
            color ∈ system.positiveSignature positive)).card := by
    rw [system.balanced color]
    exact Finset.card_pos.mpr hnegativeNonempty
  obtain ⟨positive, hpositive⟩ :=
    Finset.card_pos.mp hpositiveCard
  exact ⟨positive, (Finset.mem_filter.mp hpositive).2⟩

private theorem not_three_distinct_pairs_through
    (hcolorCard : Fintype.card Color ≤ 3)
    (color : Color) (first second third : Finset Color)
    (hfirstCard : first.card = 2)
    (hsecondCard : second.card = 2)
    (hthirdCard : third.card = 2)
    (hcolorFirst : color ∈ first)
    (hcolorSecond : color ∈ second)
    (hcolorThird : color ∈ third)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) : False := by
  have hfirstErase : (first.erase color).card = 1 := by
    rw [Finset.card_erase_of_mem hcolorFirst, hfirstCard]
  have hsecondErase : (second.erase color).card = 1 := by
    rw [Finset.card_erase_of_mem hcolorSecond, hsecondCard]
  have hthirdErase : (third.erase color).card = 1 := by
    rw [Finset.card_erase_of_mem hcolorThird, hthirdCard]
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hfirstErase
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hsecondErase
  obtain ⟨d, hd⟩ := Finset.card_eq_one.mp hthirdErase
  have hfirst : first = {color, a} := by
    rw [← Finset.insert_erase hcolorFirst, ha]
  have hsecond : second = {color, b} := by
    rw [← Finset.insert_erase hcolorSecond, hb]
  have hthird : third = {color, d} := by
    rw [← Finset.insert_erase hcolorThird, hd]
  have hac : color ≠ a := by
    have : color ∉ first.erase color := Finset.notMem_erase color first
    simpa [ha] using this
  have hbc : color ≠ b := by
    have : color ∉ second.erase color := Finset.notMem_erase color second
    simpa [hb] using this
  have hdc : color ≠ d := by
    have : color ∉ third.erase color := Finset.notMem_erase color third
    simpa [hd] using this
  have hab : a ≠ b := by
    intro hab
    apply hfirstSecond
    simpa [hfirst, hsecond, hab]
  have had : a ≠ d := by
    intro had
    apply hfirstThird
    simpa [hfirst, hthird, had]
  have hbd : b ≠ d := by
    intro hbd
    apply hsecondThird
    simpa [hsecond, hthird, hbd]
  have hfour : ({color, a, b, d} : Finset Color).card = 4 := by
    simp [hac, hbc, hdc, hab, had, hbd]
  have hle :
      ({color, a, b, d} : Finset Color).card ≤ Fintype.card Color :=
    Finset.card_le_univ _
  omega

private theorem two_pairs_intersect
    (hcolorCard : Fintype.card Color ≤ 3)
    (first second : Finset Color)
    (hfirstCard : first.card = 2)
    (hsecondCard : second.card = 2) :
    ∃ color, color ∈ first ∧ color ∈ second := by
  by_contra hintersect
  have hdisjoint : Disjoint first second := by
    rw [Finset.disjoint_left]
    intro color hfirst hsecond
    exact hintersect ⟨color, hfirst, hsecond⟩
  have hunionCard : (first ∪ second).card = 4 := by
    rw [Finset.card_union_of_disjoint hdisjoint,
      hfirstCard, hsecondCard]
  have hle : (first ∪ second).card ≤ Fintype.card Color :=
    Finset.card_le_univ _
  omega

/--
Unless an equal nonempty signature already occurs on both sides, an active
balanced system over at most three colors has a singleton signature.

This is the algebraic heart of the endpoint-peeling proof: if all active
signatures had size two, three distinct two-subsets through one color would
be forced inside a three-element color type.
-/
theorem exists_common_nonempty_signature_or_singleton
    (system : ColorSignatureSystem Color Positive Negative)
    (hcolorCard : Fintype.card Color ≤ 3)
    (hactive :
      (∃ positive, (system.positiveSignature positive).Nonempty) ∨
        ∃ negative, (system.negativeSignature negative).Nonempty) :
    (∃ positive negative,
        system.positiveSignature positive =
            system.negativeSignature negative ∧
          (system.positiveSignature positive).Nonempty) ∨
      (∃ positive color,
        system.positiveSignature positive = {color}) ∨
      ∃ negative color,
        system.negativeSignature negative = {color} := by
  by_cases hcommon :
      ∃ positive negative,
        system.positiveSignature positive =
            system.negativeSignature negative ∧
          (system.positiveSignature positive).Nonempty
  · exact Or.inl hcommon
  right
  by_cases hpositiveSingleton :
      ∃ positive color,
        system.positiveSignature positive = {color}
  · exact Or.inl hpositiveSingleton
  right
  by_cases hnegativeSingleton :
      ∃ negative color,
        system.negativeSignature negative = {color}
  · exact hnegativeSingleton
  exfalso
  have hpositiveCardTwo :
      ∀ positive,
        (system.positiveSignature positive).Nonempty →
          (system.positiveSignature positive).card = 2 := by
    intro positive hnonempty
    have hpositive : 0 < (system.positiveSignature positive).card :=
      Finset.card_pos.mpr hnonempty
    have hnotOne :
        (system.positiveSignature positive).card ≠ 1 := by
      intro hone
      obtain ⟨color, hsignature⟩ := Finset.card_eq_one.mp hone
      exact hpositiveSingleton ⟨positive, color, hsignature⟩
    exact Nat.eq_of_le_of_lt_succ
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨Nat.ne_of_gt hpositive, hnotOne⟩)
      (Nat.lt_succ_iff.mpr (system.positive_card_le_two positive))
  have hnegativeCardTwo :
      ∀ negative,
        (system.negativeSignature negative).Nonempty →
          (system.negativeSignature negative).card = 2 := by
    intro negative hnonempty
    have hnegative : 0 < (system.negativeSignature negative).card :=
      Finset.card_pos.mpr hnonempty
    have hnotOne :
        (system.negativeSignature negative).card ≠ 1 := by
      intro hone
      obtain ⟨color, hsignature⟩ := Finset.card_eq_one.mp hone
      exact hnegativeSingleton ⟨negative, color, hsignature⟩
    exact Nat.eq_of_le_of_lt_succ
      (Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨Nat.ne_of_gt hnegative, hnotOne⟩)
      (Nat.lt_succ_iff.mpr (system.negative_card_le_two negative))
  have hpositiveOfNegative :
      ∀ {color negative},
        color ∈ system.negativeSignature negative →
          ∃ positive,
            color ∈ system.positiveSignature positive := by
    intro color negative hnegative
    have hnegativeNonempty :
        (Finset.univ.filter
          (fun other =>
            color ∈ system.negativeSignature other)).Nonempty :=
      ⟨negative, by simp [hnegative]⟩
    have hpositiveCard :
        0 <
          (Finset.univ.filter
            (fun positive =>
              color ∈ system.positiveSignature positive)).card := by
      rw [system.balanced color]
      exact Finset.card_pos.mpr hnegativeNonempty
    obtain ⟨positive, hpositive⟩ :=
      Finset.card_pos.mp hpositiveCard
    exact ⟨positive, (Finset.mem_filter.mp hpositive).2⟩
  have hnegativeOfPositive :
      ∀ {color positive},
        color ∈ system.positiveSignature positive →
          ∃ negative,
            color ∈ system.negativeSignature negative := by
    intro color positive hpositive
    have hpositiveNonempty :
        (Finset.univ.filter
          (fun other =>
            color ∈ system.positiveSignature other)).Nonempty :=
      ⟨positive, by simp [hpositive]⟩
    have hnegativeCard :
        0 <
          (Finset.univ.filter
            (fun negative =>
              color ∈ system.negativeSignature negative)).card := by
      rw [← system.balanced color]
      exact Finset.card_pos.mpr hpositiveNonempty
    obtain ⟨negative, hnegative⟩ :=
      Finset.card_pos.mp hnegativeCard
    exact ⟨negative, (Finset.mem_filter.mp hnegative).2⟩
  obtain ⟨positive, hpositiveNonempty⟩ :
      ∃ positive, (system.positiveSignature positive).Nonempty := by
    rcases hactive with hpositive | hnegative
    · exact hpositive
    · obtain ⟨negative, hnegativeNonempty⟩ := hnegative
      obtain ⟨color, hcolor⟩ := hnegativeNonempty
      obtain ⟨positive, hpositiveColor⟩ :=
        hpositiveOfNegative hcolor
      exact ⟨positive, ⟨color, hpositiveColor⟩⟩
  obtain ⟨firstColor, secondColor, hcolorsNe, hpositiveSignature⟩ :=
    Finset.card_eq_two.mp
      (hpositiveCardTwo positive hpositiveNonempty)
  have hfirstPositive :
      firstColor ∈ system.positiveSignature positive := by
    simp [hpositiveSignature]
  have hsecondPositive :
      secondColor ∈ system.positiveSignature positive := by
    simp [hpositiveSignature]
  obtain ⟨firstNegative, hfirstNegative⟩ :=
    hnegativeOfPositive hfirstPositive
  obtain ⟨secondNegative, hsecondNegative⟩ :=
    hnegativeOfPositive hsecondPositive
  have hfirstNegativeNonempty :
      (system.negativeSignature firstNegative).Nonempty :=
    ⟨firstColor, hfirstNegative⟩
  have hsecondNegativeNonempty :
      (system.negativeSignature secondNegative).Nonempty :=
    ⟨secondColor, hsecondNegative⟩
  have hfirstNegativeCard :
      (system.negativeSignature firstNegative).card = 2 :=
    hnegativeCardTwo firstNegative hfirstNegativeNonempty
  have hsecondNegativeCard :
      (system.negativeSignature secondNegative).card = 2 :=
    hnegativeCardTwo secondNegative hsecondNegativeNonempty
  have hpositiveNeFirst :
      system.positiveSignature positive ≠
        system.negativeSignature firstNegative := by
    intro heq
    exact hcommon
      ⟨positive, firstNegative, heq, hpositiveNonempty⟩
  have hpositiveNeSecond :
      system.positiveSignature positive ≠
        system.negativeSignature secondNegative := by
    intro heq
    exact hcommon
      ⟨positive, secondNegative, heq, hpositiveNonempty⟩
  have hnegativeNe :
      system.negativeSignature firstNegative ≠
        system.negativeSignature secondNegative := by
    intro heq
    have hfirstInSecond :
        firstColor ∈ system.negativeSignature secondNegative := by
      simpa [heq] using hfirstNegative
    have hpositiveSubset :
        system.positiveSignature positive ⊆
          system.negativeSignature secondNegative := by
      intro color hcolor
      rw [hpositiveSignature] at hcolor
      simp only [Finset.mem_insert, Finset.mem_singleton] at hcolor
      rcases hcolor with rfl | rfl
      · exact hfirstInSecond
      · exact hsecondNegative
    have hequal :=
      Finset.eq_of_subset_of_card_le hpositiveSubset
        (by rw [hpositiveCardTwo positive hpositiveNonempty,
          hsecondNegativeCard])
    exact hpositiveNeSecond hequal
  obtain ⟨sharedColor, hsharedFirst, hsharedSecond⟩ :=
    two_pairs_intersect hcolorCard
      (system.negativeSignature firstNegative)
      (system.negativeSignature secondNegative)
      hfirstNegativeCard hsecondNegativeCard
  obtain ⟨secondPositive, hsharedPositive⟩ :=
    hpositiveOfNegative hsharedFirst
  have hsecondPositiveNonempty :
      (system.positiveSignature secondPositive).Nonempty :=
    ⟨sharedColor, hsharedPositive⟩
  have hsecondPositiveCard :
      (system.positiveSignature secondPositive).card = 2 :=
    hpositiveCardTwo secondPositive hsecondPositiveNonempty
  have hsecondPositiveNeFirst :
      system.positiveSignature secondPositive ≠
        system.negativeSignature firstNegative := by
    intro heq
    exact hcommon
      ⟨secondPositive, firstNegative, heq,
        hsecondPositiveNonempty⟩
  have hsecondPositiveNeSecond :
      system.positiveSignature secondPositive ≠
        system.negativeSignature secondNegative := by
    intro heq
    exact hcommon
      ⟨secondPositive, secondNegative, heq,
        hsecondPositiveNonempty⟩
  exact not_three_distinct_pairs_through hcolorCard sharedColor
    (system.negativeSignature firstNegative)
    (system.negativeSignature secondNegative)
    (system.positiveSignature secondPositive)
    hfirstNegativeCard hsecondNegativeCard hsecondPositiveCard
    hsharedFirst hsharedSecond hsharedPositive
    hnegativeNe hsecondPositiveNeFirst.symm
    hsecondPositiveNeSecond.symm

/-- Total number of color incidences in all signatures. -/
def incidenceWeight
    (system : ColorSignatureSystem Color Positive Negative) : ℕ :=
  (∑ positive, (system.positiveSignature positive).card) +
    ∑ negative, (system.negativeSignature negative).card

/--
Delete the same set of colors from one positive and one negative endpoint.
Colorwise balance is preserved because exactly one incidence is deleted on
each side for every deleted color.
-/
noncomputable def eraseEndpointColors
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative) :
    ColorSignatureSystem Color Positive Negative := by
  classical
  refine {
    positiveSignature := fun other =>
      if other = positive then
        system.positiveSignature other \ removed
      else
        system.positiveSignature other
    negativeSignature := fun other =>
      if other = negative then
        system.negativeSignature other \ removed
      else
        system.negativeSignature other
    positive_card_le_two := ?_
    negative_card_le_two := ?_
    balanced := ?_
  }
  · intro other
    split
    · exact (Finset.card_le_card Finset.sdiff_subset).trans
        (system.positive_card_le_two other)
    · exact system.positive_card_le_two other
  · intro other
    split
    · exact (Finset.card_le_card Finset.sdiff_subset).trans
        (system.negative_card_le_two other)
    · exact system.negative_card_le_two other
  · intro color
    by_cases hremoved : color ∈ removed
    · have hpositiveMem :
          positive ∈
            Finset.univ.filter
              (fun other =>
                color ∈ system.positiveSignature other) := by
        simp [hpositive hremoved]
      have hnegativeMem :
          negative ∈
            Finset.univ.filter
              (fun other =>
                color ∈ system.negativeSignature other) := by
        simp [hnegative hremoved]
      have hpositiveFilter :
          Finset.univ.filter
              (fun other =>
                color ∈
                  (if other = positive then
                    system.positiveSignature other \ removed
                  else
                    system.positiveSignature other)) =
            (Finset.univ.filter
              (fun other =>
                color ∈ system.positiveSignature other)).erase
              positive := by
        ext other
        by_cases hother : other = positive
        · subst other
          simp [hremoved]
        · simp [hother]
      have hnegativeFilter :
          Finset.univ.filter
              (fun other =>
                color ∈
                  (if other = negative then
                    system.negativeSignature other \ removed
                  else
                    system.negativeSignature other)) =
            (Finset.univ.filter
              (fun other =>
                color ∈ system.negativeSignature other)).erase
              negative := by
        ext other
        by_cases hother : other = negative
        · subst other
          simp [hremoved]
        · simp [hother]
      rw [hpositiveFilter, hnegativeFilter,
        Finset.card_erase_of_mem hpositiveMem,
        Finset.card_erase_of_mem hnegativeMem,
        system.balanced color]
    · have hpositiveFilter :
          Finset.univ.filter
              (fun other =>
                color ∈
                  (if other = positive then
                    system.positiveSignature other \ removed
                  else
                    system.positiveSignature other)) =
            Finset.univ.filter
              (fun other =>
                color ∈ system.positiveSignature other) := by
        ext other
        by_cases hother : other = positive
        · subst other
          simp [hremoved]
        · simp [hother]
      have hnegativeFilter :
          Finset.univ.filter
              (fun other =>
                color ∈
                  (if other = negative then
                    system.negativeSignature other \ removed
                  else
                    system.negativeSignature other)) =
            Finset.univ.filter
              (fun other =>
                color ∈ system.negativeSignature other) := by
        ext other
        by_cases hother : other = negative
        · subst other
          simp [hremoved]
        · simp [hother]
      rw [hpositiveFilter, hnegativeFilter, system.balanced color]

@[simp] theorem eraseEndpointColors_positive_at
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative) :
    (system.eraseEndpointColors positive negative removed
      hpositive hnegative).positiveSignature positive =
        system.positiveSignature positive \ removed := by
  classical
  simp [eraseEndpointColors]

@[simp] theorem eraseEndpointColors_negative_at
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative) :
    (system.eraseEndpointColors positive negative removed
      hpositive hnegative).negativeSignature negative =
        system.negativeSignature negative \ removed := by
  classical
  simp [eraseEndpointColors]

theorem eraseEndpointColors_positive_subset
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (other : Positive) :
    (system.eraseEndpointColors positive negative removed
      hpositive hnegative).positiveSignature other ⊆
        system.positiveSignature other := by
  classical
  by_cases hother : other = positive
  · subst other
    simp [eraseEndpointColors]
  · simp [eraseEndpointColors, hother]

theorem eraseEndpointColors_negative_subset
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (other : Negative) :
    (system.eraseEndpointColors positive negative removed
      hpositive hnegative).negativeSignature other ⊆
        system.negativeSignature other := by
  classical
  by_cases hother : other = negative
  · subst other
    simp [eraseEndpointColors]
  · simp [eraseEndpointColors, hother]

/-- Deleting a nonempty endpoint-color set strictly lowers incidence weight. -/
theorem eraseEndpointColors_incidenceWeight_lt
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (hremoved : removed.Nonempty) :
    (system.eraseEndpointColors positive negative removed
      hpositive hnegative).incidenceWeight <
        system.incidenceWeight := by
  classical
  have hpositivePoint :
      ((system.eraseEndpointColors positive negative removed
        hpositive hnegative).positiveSignature positive).card <
          (system.positiveSignature positive).card := by
    rw [eraseEndpointColors_positive_at]
    rw [Finset.card_sdiff,
      Finset.inter_eq_left.mpr hpositive]
    have hremovedPos : 0 < removed.card :=
      Finset.card_pos.mpr hremoved
    have hremovedLe :
        removed.card ≤
          (system.positiveSignature positive).card :=
      Finset.card_le_card hpositive
    omega
  have hpositiveSum :
      (∑ other,
        ((system.eraseEndpointColors positive negative removed
          hpositive hnegative).positiveSignature other).card) <
        ∑ other, (system.positiveSignature other).card := by
    apply Finset.sum_lt_sum
    · intro other _
      exact Finset.card_le_card
        (eraseEndpointColors_positive_subset system positive negative
          removed hpositive hnegative other)
    · exact ⟨positive, Finset.mem_univ _, hpositivePoint⟩
  have hnegativeSum :
      (∑ other,
        ((system.eraseEndpointColors positive negative removed
          hpositive hnegative).negativeSignature other).card) ≤
        ∑ other, (system.negativeSignature other).card := by
    apply Finset.sum_le_sum
    intro other _
    exact Finset.card_le_card
      (eraseEndpointColors_negative_subset system positive negative
        removed hpositive hnegative other)
  unfold incidenceWeight
  exact Nat.add_lt_add_of_lt_of_le hpositiveSum hnegativeSum

end ColorSignatureSystem

/--
A colorwise perfect matching, represented relationally so that several
colors may reuse the same underlying positive-negative edge.
-/
structure ColorwiseMatching
    {Color : Type uC} {Positive : Type uP} {Negative : Type uN}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]
    (system : ColorSignatureSystem Color Positive Negative) where
  /-- A color-labelled positive-negative matching edge. -/
  Match : Color → Positive → Negative → Prop
  /-- Every matched edge has the required color at both endpoints. -/
  match_mem :
    ∀ {color positive negative},
      Match color positive negative →
        color ∈ system.positiveSignature positive ∧
          color ∈ system.negativeSignature negative
  /-- Every eligible positive endpoint has exactly one partner. -/
  positive_unique :
    ∀ color positive,
      color ∈ system.positiveSignature positive →
        ∃! negative, Match color positive negative
  /-- Every eligible negative endpoint has exactly one partner. -/
  negative_unique :
    ∀ color negative,
      color ∈ system.negativeSignature negative →
        ∃! positive, Match color positive negative

namespace ColorwiseMatching

variable
    {Color : Type uC} {Positive : Type uP} {Negative : Type uN}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]
    {system : ColorSignatureSystem Color Positive Negative}

/-- An arbitrary colorwise matching obtained independently in every color. -/
noncomputable def arbitrary
    (system : ColorSignatureSystem Color Positive Negative) :
    ColorwiseMatching system where
  Match color positive negative :=
    ∃ hpositive : color ∈ system.positiveSignature positive,
      (Fintype.equivOfCardEq
        (system.eligible_card_eq color)
        ⟨positive, hpositive⟩).1 = negative
  match_mem := by
    rintro color positive negative ⟨hpositive, hpartner⟩
    refine ⟨hpositive, ?_⟩
    have hnegative :=
      (Fintype.equivOfCardEq
        (system.eligible_card_eq color)
        ⟨positive, hpositive⟩).2
    simpa [hpartner] using hnegative
  positive_unique := by
    intro color positive hpositive
    let partner :=
      Fintype.equivOfCardEq
        (system.eligible_card_eq color)
        ⟨positive, hpositive⟩
    refine ⟨partner.1, ⟨hpositive, rfl⟩, ?_⟩
    intro other hother
    rcases hother with ⟨_, hother⟩
    exact hother.symm
  negative_unique := by
    intro color negative hnegative
    let partner :=
      (Fintype.equivOfCardEq
        (system.eligible_card_eq color)).symm
        ⟨negative, hnegative⟩
    refine ⟨partner.1, ?_, ?_⟩
    · refine ⟨partner.2, ?_⟩
      simp [partner]
    · intro other hother
      rcases hother with ⟨hotherMem, hotherPartner⟩
      have hsubtype :
          (⟨other, hotherMem⟩ :
            {positive : Positive //
              color ∈ system.positiveSignature positive}) =
            partner := by
        apply
          (Fintype.equivOfCardEq
            (system.eligible_card_eq color)).injective
        apply Subtype.ext
        simpa [partner] using hotherPartner
      exact congrArg Subtype.val hsubtype

/--
Restore the deleted endpoint colors by assigning all of them to the same
underlying positive-negative edge.  Several color labels may therefore
reuse one simple edge.
-/
noncomputable def restoreEndpointColors
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (matching :
      ColorwiseMatching
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative)) :
    ColorwiseMatching system where
  Match color otherPositive otherNegative :=
    matching.Match color otherPositive otherNegative ∨
      (otherPositive = positive ∧
        otherNegative = negative ∧ color ∈ removed)
  match_mem := by
    intro color otherPositive otherNegative hmatch
    rcases hmatch with hmatch | ⟨rfl, rfl, hremoved⟩
    · exact
        ⟨system.eraseEndpointColors_positive_subset
            positive negative removed hpositive hnegative
            otherPositive (matching.match_mem hmatch).1,
          system.eraseEndpointColors_negative_subset
            positive negative removed hpositive hnegative
            otherNegative (matching.match_mem hmatch).2⟩
    · exact ⟨hpositive hremoved, hnegative hremoved⟩
  positive_unique := by
    intro color otherPositive hcolor
    by_cases hreduced :
        color ∈
          (system.eraseEndpointColors positive negative removed
            hpositive hnegative).positiveSignature otherPositive
    · obtain ⟨partner, hpartner, hunique⟩ :=
        matching.positive_unique color otherPositive hreduced
      refine ⟨partner, Or.inl hpartner, ?_⟩
      intro other hother
      rcases hother with hother | ⟨hotherPositive, _, hremoved⟩
      · exact hunique other hother
      · subst otherPositive
        have hnotRemoved : color ∉ removed := by
          rw [system.eraseEndpointColors_positive_at] at hreduced
          exact (Finset.mem_sdiff.mp hreduced).2
        exact False.elim (hnotRemoved hremoved)
    · have hotherPositive : otherPositive = positive := by
        by_contra hne
        apply hreduced
        simpa [ColorSignatureSystem.eraseEndpointColors, hne] using
          hcolor
      subst otherPositive
      have hremoved : color ∈ removed := by
        by_contra hnotRemoved
        apply hreduced
        rw [system.eraseEndpointColors_positive_at]
        exact Finset.mem_sdiff.mpr ⟨hcolor, hnotRemoved⟩
      refine ⟨negative, Or.inr ⟨rfl, rfl, hremoved⟩, ?_⟩
      intro other hother
      rcases hother with hother | ⟨_, hotherNegative, _⟩
      · exact False.elim
          (hreduced (matching.match_mem hother).1)
      · exact hotherNegative
  negative_unique := by
    intro color otherNegative hcolor
    by_cases hreduced :
        color ∈
          (system.eraseEndpointColors positive negative removed
            hpositive hnegative).negativeSignature otherNegative
    · obtain ⟨partner, hpartner, hunique⟩ :=
        matching.negative_unique color otherNegative hreduced
      refine ⟨partner, Or.inl hpartner, ?_⟩
      intro other hother
      rcases hother with hother | ⟨_, hotherNegative, hremoved⟩
      · exact hunique other hother
      · subst otherNegative
        have hnotRemoved : color ∉ removed := by
          rw [system.eraseEndpointColors_negative_at] at hreduced
          exact (Finset.mem_sdiff.mp hreduced).2
        exact False.elim (hnotRemoved hremoved)
    · have hotherNegative : otherNegative = negative := by
        by_contra hne
        apply hreduced
        simpa [ColorSignatureSystem.eraseEndpointColors, hne] using
          hcolor
      subst otherNegative
      have hremoved : color ∈ removed := by
        by_contra hnotRemoved
        apply hreduced
        rw [system.eraseEndpointColors_negative_at]
        exact Finset.mem_sdiff.mpr ⟨hcolor, hnotRemoved⟩
      refine ⟨positive, Or.inr ⟨rfl, rfl, hremoved⟩, ?_⟩
      intro other hother
      rcases hother with hother | ⟨hotherPositive, _, _⟩
      · exact False.elim
          (hreduced (matching.match_mem hother).2)
      · exact hotherPositive

/-- The simple union of all color-labelled matching edges. -/
def simpleGraph (matching : ColorwiseMatching system) :
    SimpleGraph (Positive ⊕ Negative) where
  Adj
    | Sum.inl positive, Sum.inr negative =>
        ∃ color, matching.Match color positive negative
    | Sum.inr negative, Sum.inl positive =>
        ∃ color, matching.Match color positive negative
    | _, _ => False
  symm := by
    intro left right hadj
    cases left <;> cases right <;> simpa using hadj
  loopless := by
    constructor
    intro vertex
    cases vertex <;> simp

noncomputable instance instDecidableRelSimpleGraph
    (matching : ColorwiseMatching system) :
    DecidableRel matching.simpleGraph.Adj :=
  Classical.decRel _

theorem simpleGraph_adj_inl_inr
    (matching : ColorwiseMatching system)
    (positive : Positive) (negative : Negative) :
    matching.simpleGraph.Adj (Sum.inl positive) (Sum.inr negative) ↔
      ∃ color, matching.Match color positive negative := by
  rfl

theorem simpleGraph_not_adj_inl_inl
    (matching : ColorwiseMatching system)
    (left right : Positive) :
    ¬matching.simpleGraph.Adj (Sum.inl left) (Sum.inl right) := by
  simp [simpleGraph]

theorem simpleGraph_not_adj_inr_inr
    (matching : ColorwiseMatching system)
    (left right : Negative) :
    ¬matching.simpleGraph.Adj (Sum.inr left) (Sum.inr right) := by
  simp [simpleGraph]

/-- Restoring a nonempty deleted color set adds exactly one simple edge. -/
theorem simpleGraph_restoreEndpointColors
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (matching :
      ColorwiseMatching
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative))
    (hremoved : removed.Nonempty) :
    (restoreEndpointColors system positive negative removed
        hpositive hnegative matching).simpleGraph =
      matching.simpleGraph ⊔
        SimpleGraph.edge (Sum.inl positive) (Sum.inr negative) := by
  ext left right
  cases left with
  | inl leftPositive =>
      cases right with
      | inl rightPositive =>
          simp [simpleGraph, restoreEndpointColors,
            SimpleGraph.edge_adj]
      | inr rightNegative =>
          simp only [simpleGraph, restoreEndpointColors,
            SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
            Sum.inr_ne_inl, and_false, false_and, or_false, false_or,
            ne_eq, not_false_eq_true, and_true]
          constructor
          · rintro ⟨color, hmatch | ⟨hleft, hright, _⟩⟩
            · exact Or.inl ⟨color, hmatch⟩
            · exact Or.inr ⟨hleft, hright⟩
          · rintro (⟨color, hmatch⟩ | ⟨hleft, hright⟩)
            · exact ⟨color, Or.inl hmatch⟩
            · obtain ⟨color, hcolor⟩ := hremoved
              exact ⟨color, Or.inr ⟨hleft, hright, hcolor⟩⟩
  | inr leftNegative =>
      cases right with
      | inl rightPositive =>
          simp only [simpleGraph, restoreEndpointColors,
            SimpleGraph.sup_adj, SimpleGraph.edge_adj,
            Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr,
            Sum.inr_ne_inl, and_false, false_and, or_false, false_or,
            ne_eq, not_false_eq_true, and_true]
          constructor
          · rintro ⟨color, hmatch | ⟨hright, hleft, _⟩⟩
            · exact Or.inl ⟨color, hmatch⟩
            · exact Or.inr ⟨hleft, hright⟩
          · rintro (⟨color, hmatch⟩ | ⟨hleft, hright⟩)
            · exact ⟨color, Or.inl hmatch⟩
            · obtain ⟨color, hcolor⟩ := hremoved
              exact ⟨color, Or.inr ⟨hright, hleft, hcolor⟩⟩
      | inr rightNegative =>
          simp [simpleGraph, restoreEndpointColors,
            SimpleGraph.edge_adj]

private noncomputable def neighborColorAtPositive
    (matching : ColorwiseMatching system)
    (positive : Positive)
    (neighbor :
      matching.simpleGraph.neighborSet (Sum.inl positive)) :
    {color // color ∈ system.positiveSignature positive} := by
  rcases neighbor with ⟨vertex, hmem⟩
  have hadj :
      matching.simpleGraph.Adj (Sum.inl positive) vertex :=
    (matching.simpleGraph.mem_neighborSet _ _).mp hmem
  cases vertex with
  | inl other =>
      exact False.elim
        (matching.simpleGraph_not_adj_inl_inl positive other hadj)
  | inr negative =>
      let color :=
        Classical.choose
          ((matching.simpleGraph_adj_inl_inr positive negative).mp hadj)
      exact ⟨color,
        (matching.match_mem
          (Classical.choose_spec
            ((matching.simpleGraph_adj_inl_inr positive negative).mp
              hadj))).1⟩

private theorem neighborColorAtPositive_injective
    (matching : ColorwiseMatching system)
    (positive : Positive) :
    Function.Injective
      (matching.neighborColorAtPositive positive) := by
  intro left right hcolor
  apply Subtype.ext
  cases left with
  | mk leftVertex leftAdj =>
      cases right with
      | mk rightVertex rightAdj =>
          cases leftVertex with
          | inl leftPositive =>
              have leftAdj' :
                  matching.simpleGraph.Adj
                    (Sum.inl positive) (Sum.inl leftPositive) :=
                (matching.simpleGraph.mem_neighborSet _ _).mp leftAdj
              exact False.elim
                (matching.simpleGraph_not_adj_inl_inl
                  positive leftPositive leftAdj')
          | inr leftNegative =>
              cases rightVertex with
              | inl rightPositive =>
                  have rightAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inl positive) (Sum.inl rightPositive) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp rightAdj
                  exact False.elim
                    (matching.simpleGraph_not_adj_inl_inl
                      positive rightPositive rightAdj')
              | inr rightNegative =>
                  have leftAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inl positive) (Sum.inr leftNegative) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp leftAdj
                  have rightAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inl positive) (Sum.inr rightNegative) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp rightAdj
                  have hleftMatch :=
                    Classical.choose_spec
                      ((matching.simpleGraph_adj_inl_inr
                        positive leftNegative).mp leftAdj')
                  have hrightMatch :=
                    Classical.choose_spec
                      ((matching.simpleGraph_adj_inl_inr
                        positive rightNegative).mp rightAdj')
                  have hcolorValue := congrArg Subtype.val hcolor
                  simp only [neighborColorAtPositive] at hcolorValue
                  change
                      Classical.choose
                        ((matching.simpleGraph_adj_inl_inr
                          positive leftNegative).mp leftAdj') =
                      Classical.choose
                        ((matching.simpleGraph_adj_inl_inr
                          positive rightNegative).mp rightAdj') at hcolorValue
                  rw [← hcolorValue] at hrightMatch
                  exact congrArg Sum.inr <|
                    (matching.positive_unique
                        _ positive
                        (matching.match_mem hleftMatch).1).unique
                      hleftMatch hrightMatch

private noncomputable def neighborColorAtNegative
    (matching : ColorwiseMatching system)
    (negative : Negative)
    (neighbor :
      matching.simpleGraph.neighborSet (Sum.inr negative)) :
    {color // color ∈ system.negativeSignature negative} := by
  rcases neighbor with ⟨vertex, hmem⟩
  have hadj :
      matching.simpleGraph.Adj (Sum.inr negative) vertex :=
    (matching.simpleGraph.mem_neighborSet _ _).mp hmem
  cases vertex with
  | inl positive =>
      let color :=
        Classical.choose
          ((matching.simpleGraph_adj_inl_inr positive negative).mp hadj.symm)
      exact ⟨color,
        (matching.match_mem
          (Classical.choose_spec
            ((matching.simpleGraph_adj_inl_inr positive negative).mp
              hadj.symm))).2⟩
  | inr other =>
      exact False.elim
        (matching.simpleGraph_not_adj_inr_inr negative other hadj)

private theorem neighborColorAtNegative_injective
    (matching : ColorwiseMatching system)
    (negative : Negative) :
    Function.Injective
      (matching.neighborColorAtNegative negative) := by
  intro left right hcolor
  apply Subtype.ext
  cases left with
  | mk leftVertex leftAdj =>
      cases right with
      | mk rightVertex rightAdj =>
          cases leftVertex with
          | inl leftPositive =>
              cases rightVertex with
              | inl rightPositive =>
                  have leftAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inr negative) (Sum.inl leftPositive) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp leftAdj
                  have rightAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inr negative) (Sum.inl rightPositive) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp rightAdj
                  have hleftMatch :=
                    Classical.choose_spec
                      ((matching.simpleGraph_adj_inl_inr
                        leftPositive negative).mp leftAdj'.symm)
                  have hrightMatch :=
                    Classical.choose_spec
                      ((matching.simpleGraph_adj_inl_inr
                        rightPositive negative).mp rightAdj'.symm)
                  have hcolorValue := congrArg Subtype.val hcolor
                  simp only [neighborColorAtNegative] at hcolorValue
                  change
                      Classical.choose
                        ((matching.simpleGraph_adj_inl_inr
                          leftPositive negative).mp leftAdj'.symm) =
                      Classical.choose
                        ((matching.simpleGraph_adj_inl_inr
                          rightPositive negative).mp rightAdj'.symm) at hcolorValue
                  rw [← hcolorValue] at hrightMatch
                  exact congrArg Sum.inl <|
                    (matching.negative_unique
                        _ negative
                        (matching.match_mem hleftMatch).2).unique
                      hleftMatch hrightMatch
              | inr rightNegative =>
                  have rightAdj' :
                      matching.simpleGraph.Adj
                        (Sum.inr negative) (Sum.inr rightNegative) :=
                    (matching.simpleGraph.mem_neighborSet _ _).mp rightAdj
                  exact False.elim
                    (matching.simpleGraph_not_adj_inr_inr
                      negative rightNegative rightAdj')
          | inr leftNegative =>
              have leftAdj' :
                  matching.simpleGraph.Adj
                    (Sum.inr negative) (Sum.inr leftNegative) :=
                (matching.simpleGraph.mem_neighborSet _ _).mp leftAdj
              exact False.elim
                (matching.simpleGraph_not_adj_inr_inr
                  negative leftNegative leftAdj')

/-- Every vertex of the simple union has degree at most its signature size. -/
theorem degree_le_signature_card
    (matching : ColorwiseMatching system) :
    ∀ vertex : Positive ⊕ Negative,
      matching.simpleGraph.degree vertex ≤
        match vertex with
        | Sum.inl positive => (system.positiveSignature positive).card
        | Sum.inr negative => (system.negativeSignature negative).card := by
  intro vertex
  cases vertex with
  | inl positive =>
      simp only
      rw [← matching.simpleGraph.card_neighborSet_eq_degree]
      rw [← Fintype.card_coe]
      exact Fintype.card_le_of_injective
        (matching.neighborColorAtPositive positive)
        (matching.neighborColorAtPositive_injective positive)
  | inr negative =>
      simp only
      rw [← matching.simpleGraph.card_neighborSet_eq_degree]
      rw [← Fintype.card_coe]
      exact Fintype.card_le_of_injective
        (matching.neighborColorAtNegative negative)
        (matching.neighborColorAtNegative_injective negative)

/-- The simple union is a bipartite linear forest. -/
def IsBipartiteLinearForest
    (matching : ColorwiseMatching system) : Prop :=
  matching.simpleGraph.IsAcyclic ∧
    ∀ vertex, matching.simpleGraph.degree vertex ≤ 2

theorem isBipartiteLinearForest_of_isAcyclic
    (matching : ColorwiseMatching system)
    (hacyclic : matching.simpleGraph.IsAcyclic) :
    matching.IsBipartiteLinearForest := by
  refine ⟨hacyclic, ?_⟩
  intro vertex
  exact (matching.degree_le_signature_card vertex).trans <|
    match vertex with
    | Sum.inl positive => system.positive_card_le_two positive
    | Sum.inr negative => system.negative_card_le_two negative

/--
Adding back endpoint colors preserves acyclicity when the chosen positive
endpoint becomes isolated in the reduced system.
-/
theorem restoreEndpointColors_isAcyclic_of_positive_exact
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (hpositiveExact :
      system.positiveSignature positive = removed)
    (hremoved : removed.Nonempty)
    (matching :
      ColorwiseMatching
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative))
    (hacyclic : matching.simpleGraph.IsAcyclic) :
    (restoreEndpointColors system positive negative removed
      hpositive hnegative matching).simpleGraph.IsAcyclic := by
  rw [simpleGraph_restoreEndpointColors system positive negative
    removed hpositive hnegative matching hremoved]
  apply hacyclic.sup_edge_of_not_reachable
  apply SimpleGraph.not_reachable_of_left_degree_zero
  · simp
  · have hdegree :=
      matching.degree_le_signature_card (Sum.inl positive)
    have hsignature :
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative).positiveSignature positive = ∅ := by
      rw [system.eraseEndpointColors_positive_at, hpositiveExact]
      simp
    change
      matching.simpleGraph.degree (Sum.inl positive) ≤
        ((system.eraseEndpointColors positive negative removed
          hpositive hnegative).positiveSignature positive).card at hdegree
    rw [hsignature] at hdegree
    simpa using hdegree

/--
The symmetric restoration lemma when the chosen negative endpoint becomes
isolated in the reduced system.
-/
theorem restoreEndpointColors_isAcyclic_of_negative_exact
    (system : ColorSignatureSystem Color Positive Negative)
    (positive : Positive) (negative : Negative)
    (removed : Finset Color)
    (hpositive :
      removed ⊆ system.positiveSignature positive)
    (hnegative :
      removed ⊆ system.negativeSignature negative)
    (hnegativeExact :
      system.negativeSignature negative = removed)
    (hremoved : removed.Nonempty)
    (matching :
      ColorwiseMatching
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative))
    (hacyclic : matching.simpleGraph.IsAcyclic) :
    (restoreEndpointColors system positive negative removed
      hpositive hnegative matching).simpleGraph.IsAcyclic := by
  rw [simpleGraph_restoreEndpointColors system positive negative
    removed hpositive hnegative matching hremoved]
  apply hacyclic.sup_edge_of_not_reachable
  apply SimpleGraph.not_reachable_of_right_degree_zero
  · simp
  · have hdegree :=
      matching.degree_le_signature_card (Sum.inr negative)
    have hsignature :
        (system.eraseEndpointColors positive negative removed
          hpositive hnegative).negativeSignature negative = ∅ := by
      rw [system.eraseEndpointColors_negative_at, hnegativeExact]
      simp
    change
      matching.simpleGraph.degree (Sum.inr negative) ≤
        ((system.eraseEndpointColors positive negative removed
          hpositive hnegative).negativeSignature negative).card at hdegree
    rw [hsignature] at hdegree
    simpa using hdegree

end ColorwiseMatching

/--
Three-color selected-block forest theorem.

The proof recursively peels either a common nonempty signature or a
singleton endpoint.  The same colors are deleted from one endpoint on each
side, so balance is preserved.  One of those endpoints becomes isolated;
restoring all deleted colors on their common edge therefore cannot create a
cycle.
-/
theorem threeColor_colorwiseMatching_isAcyclic
    {Color : Type uC} {Positive : Type uP} {Negative : Type uN}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]
    (system : ColorSignatureSystem Color Positive Negative)
    (hcolorCard : Fintype.card Color ≤ 3) :
    ∃ matching : ColorwiseMatching system,
      matching.simpleGraph.IsAcyclic := by
  classical
  by_cases hactive :
      (∃ positive, (system.positiveSignature positive).Nonempty) ∨
        ∃ negative, (system.negativeSignature negative).Nonempty
  · rcases
      system.exists_common_nonempty_signature_or_singleton
        hcolorCard hactive with
      hcommon | hpositiveSingleton | hnegativeSingleton
    · obtain ⟨positive, negative, hequal, hnonempty⟩ := hcommon
      let removed := system.positiveSignature positive
      have hpositive :
          removed ⊆ system.positiveSignature positive := by
        exact Finset.Subset.rfl
      have hnegative :
          removed ⊆ system.negativeSignature negative := by
        simpa [removed, hequal]
      let reduced :=
        system.eraseEndpointColors positive negative removed
          hpositive hnegative
      obtain ⟨matching, hacyclic⟩ :=
        threeColor_colorwiseMatching_isAcyclic reduced hcolorCard
      let restored :=
        ColorwiseMatching.restoreEndpointColors system positive negative
          removed hpositive hnegative matching
      refine ⟨restored, ?_⟩
      exact
        ColorwiseMatching.restoreEndpointColors_isAcyclic_of_positive_exact
          system positive negative removed hpositive hnegative
          (by rfl) (by simpa [removed] using hnonempty)
          matching hacyclic
    · obtain ⟨positive, color, hsignature⟩ := hpositiveSingleton
      have hpositiveColor :
          color ∈ system.positiveSignature positive := by
        simp [hsignature]
      obtain ⟨negative, hnegativeColor⟩ :=
        system.exists_negative_of_positive_mem hpositiveColor
      let removed : Finset Color := {color}
      have hpositive :
          removed ⊆ system.positiveSignature positive := by
        simpa [removed, hsignature]
      have hnegative :
          removed ⊆ system.negativeSignature negative := by
        simpa [removed] using hnegativeColor
      let reduced :=
        system.eraseEndpointColors positive negative removed
          hpositive hnegative
      obtain ⟨matching, hacyclic⟩ :=
        threeColor_colorwiseMatching_isAcyclic reduced hcolorCard
      let restored :=
        ColorwiseMatching.restoreEndpointColors system positive negative
          removed hpositive hnegative matching
      refine ⟨restored, ?_⟩
      exact
        ColorwiseMatching.restoreEndpointColors_isAcyclic_of_positive_exact
          system positive negative removed hpositive hnegative
          (by simpa [removed] using hsignature)
          (by simp [removed]) matching hacyclic
    · obtain ⟨negative, color, hsignature⟩ := hnegativeSingleton
      have hnegativeColor :
          color ∈ system.negativeSignature negative := by
        simp [hsignature]
      obtain ⟨positive, hpositiveColor⟩ :=
        system.exists_positive_of_negative_mem hnegativeColor
      let removed : Finset Color := {color}
      have hpositive :
          removed ⊆ system.positiveSignature positive := by
        simpa [removed] using hpositiveColor
      have hnegative :
          removed ⊆ system.negativeSignature negative := by
        simpa [removed, hsignature]
      let reduced :=
        system.eraseEndpointColors positive negative removed
          hpositive hnegative
      obtain ⟨matching, hacyclic⟩ :=
        threeColor_colorwiseMatching_isAcyclic reduced hcolorCard
      let restored :=
        ColorwiseMatching.restoreEndpointColors system positive negative
          removed hpositive hnegative matching
      refine ⟨restored, ?_⟩
      exact
        ColorwiseMatching.restoreEndpointColors_isAcyclic_of_negative_exact
          system positive negative removed hpositive hnegative
          (by simpa [removed] using hsignature)
          (by simp [removed]) matching hacyclic
  · let matching : ColorwiseMatching system := {
      Match := fun _ _ _ => False
      match_mem := by simp
      positive_unique := by
        intro color positive hcolor
        exact False.elim <|
          hactive <| Or.inl
            ⟨positive, ⟨color, hcolor⟩⟩
      negative_unique := by
        intro color negative hcolor
        exact False.elim <|
          hactive <| Or.inr
            ⟨negative, ⟨color, hcolor⟩⟩
    }
    refine ⟨matching, ?_⟩
    have hgraph : matching.simpleGraph = ⊥ := by
      ext left right
      cases left <;> cases right <;>
        simp [ColorwiseMatching.simpleGraph, matching]
    rw [hgraph]
    exact SimpleGraph.isAcyclic_bot
termination_by system.incidenceWeight
decreasing_by
  all_goals
    exact system.eraseEndpointColors_incidenceWeight_lt
      _ _ _ _ _ (by simp_all [removed])

/-- The three-color theorem in its final bipartite-linear-forest form. -/
theorem threeColor_colorwiseMatching_linearForest
    {Color : Type uC} {Positive : Type uP} {Negative : Type uN}
    [Fintype Color] [DecidableEq Color]
    [Fintype Positive] [Fintype Negative]
    (system : ColorSignatureSystem Color Positive Negative)
    (hcolorCard : Fintype.card Color ≤ 3) :
    ∃ matching : ColorwiseMatching system,
      matching.IsBipartiteLinearForest := by
  obtain ⟨matching, hacyclic⟩ :=
    threeColor_colorwiseMatching_isAcyclic system hcolorCard
  exact ⟨matching,
    matching.isBipartiteLinearForest_of_isAcyclic hacyclic⟩

end

end XORGame
end QIT

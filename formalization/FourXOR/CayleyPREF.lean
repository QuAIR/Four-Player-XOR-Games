/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

import FourXOR.AllLengthGame

/-!
# FourXOR: the general Cayley PREF and its rank-one lattice

For a finite additive group `G`, this module proves that the standard Cayley
weight (`-1` on every `E` clause and `+1` on every `O` clause) is a PREF of
the Cayley game, and classifies the full PREF lattice: every balanced integer
weight is a scalar multiple of the standard weight, and the PREFs are exactly
its odd multiples.  The last statement is the exact lattice content behind
“the canonical PREF is unique up to sign”: the primitive generator is unique
up to sign, not every PREF is literally equal up to sign.
-/

open scoped BigOperators

namespace QIT
namespace Research
namespace FourXOR

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

attribute [local instance] Classical.propDecidable

/-- Signed balance of `z` at a player-question pair. -/
def localBalanceG (z : GameClause G → ℤ) (player question : G) : ℤ :=
  ∑ c : GameClause G, z c * if letterG c player = question then 1 else 0

/-- A PREF of the Cayley game of `G`: integer balance at every player-question
pair plus odd total target parity. -/
def IsPREFG (z : GameClause G → ℤ) : Prop :=
  (∀ player question : G, localBalanceG z player question = 0) ∧
    ((∑ c : GameClause G, z c * parityG c) % 2 = 1)

/-- The standard PREF weight: `-1` on every `E` and `+1` on every `O`. -/
def standardZG (c : GameClause G) : ℤ :=
  if c.2 then 1 else -1

@[simp]
theorem standardZG_E (g : G) : standardZG (g, false) = -1 := by
  simp [standardZG]

@[simp]
theorem standardZG_O (g : G) : standardZG (g, true) = 1 := by
  simp [standardZG]

@[simp]
theorem letterG_E (g : G) (α : G) : letterG (g, false) α = g := by
  simp [letterG]

@[simp]
theorem letterG_O (g : G) (α : G) : letterG (g, true) α = g + α := by
  simp [letterG]

@[simp]
theorem parityG_E (g : G) : parityG (g, false) = 0 := by
  simp [parityG]

@[simp]
theorem parityG_O_zero : parityG ((0 : G), true) = 1 := by
  simp [parityG]

@[simp]
theorem parityG_O_ne_zero {g : G} (hg : g ≠ 0) : parityG (g, true) = 0 := by
  simp [parityG, hg]

/-- The `E`-contribution to the balance of the standard weight is `-1`. -/
private lemma standardZG_balance_E (player question : G) :
    (∑ g : G, standardZG (g, false) *
        (if letterG (g, false) player = question then 1 else 0)) = -1 := by
  rw [Fintype.sum_eq_single question]
  · simp
  · intro g hg
    simp [letterG_E, hg]

/-- The `O`-contribution to the balance of the standard weight is `+1`. -/
private lemma standardZG_balance_O (player question : G) :
    (∑ g : G, standardZG (g, true) *
        (if letterG (g, true) player = question then 1 else 0)) = 1 := by
  rw [Fintype.sum_eq_single (question - player)]
  · simp [letterG_O, sub_add_cancel]
  · intro g hg
    have hg' : g + player ≠ question := by
      intro h
      apply hg
      exact eq_sub_of_add_eq h
    simp [letterG_O, hg']

/-- The standard weight is a PREF of the Cayley game of any finite additive
group. -/
theorem standardZG_isPREF : IsPREFG (G := G) (standardZG (G := G)) := by
  constructor
  · intro player question
    unfold localBalanceG
    rw [Fintype.sum_prod_type]
    simp
    rw [Finset.sum_add_distrib]
    have hO : (∑ x : G, if x + player = question then 1 else 0) = 1 := by
      rw [Fintype.sum_eq_single (question - player)]
      · simp [sub_add_cancel]
      · intro g hg
        have hg' : g + player ≠ question := by
          intro h
          apply hg
          exact eq_sub_of_add_eq h
        simp [hg']
    have hE : (∑ x : G, if x = question then -1 else 0) = -1 := by
      rw [Fintype.sum_eq_single question]
      · simp
      · intro g hg
        simp [hg]
    linarith [hO, hE]
  · have hO : (∑ g : G, parityG (g, true)) = 1 := by
      rw [Fintype.sum_eq_single (0 : G)]
      · simp
      · intro g hg
        simp [parityG_O_ne_zero hg]
    have hsum : (∑ c : GameClause G, standardZG c * parityG c) = 1 := by
      rw [Fintype.sum_prod_type]
      simp [hO]
    rw [hsum]
    norm_num

/-- Balance at `(player, question)` forces the `E` and `O` weights at the two
clauses of that equation to sum to zero. -/
lemma balance_E_add_O (z : GameClause G → ℤ)
    (hbalance : ∀ player question, localBalanceG z player question = 0) :
    ∀ player question, z (question, false) + z (question - player, true) = 0 := by
  intro player question
  have h := hbalance player question
  unfold localBalanceG at h
  rw [Fintype.sum_prod_type] at h
  simp at h
  rw [Finset.sum_add_distrib] at h
  have hO : (∑ x : G, if x + player = question then z (x, true) else 0) =
      z (question - player, true) := by
    rw [Fintype.sum_eq_single (question - player)]
    · simp [sub_add_cancel]
    · intro g hg
      have hg' : g + player ≠ question := by
        intro h
        apply hg
        exact eq_sub_of_add_eq h
      simp [hg']
  have hE : (∑ x : G, if x = question then z (x, false) else 0) =
      z (question, false) := by
    rw [Fintype.sum_eq_single question]
    · simp
    · intro g hg
      simp [hg]
  linarith [h, hO, hE]

/-- At every question, the `O` weight is the negation of the `E` weight. -/
lemma balance_O_eq_neg_E (z : GameClause G → ℤ)
    (hbalance : ∀ player question, localBalanceG z player question = 0) :
    ∀ question, z (question, true) = -z (question, false) := by
  intro question
  have h := balance_E_add_O z hbalance 0 question
  have h' : z (question, false) + z (question, true) = 0 := by
    simpa using h
  linarith

/-- At every question, the `E` weight equals the `E` weight at zero. -/
lemma balance_E_constant (z : GameClause G → ℤ)
    (hbalance : ∀ player question, localBalanceG z player question = 0) :
    ∀ question, z (question, false) = z (0, false) := by
  intro question
  have h := balance_E_add_O z hbalance question question
  have h' : z (question, false) + z (0, true) = 0 := by
    simpa using h
  have hO := balance_O_eq_neg_E z hbalance 0
  linarith

/-- Every balanced integer weight is a scalar multiple of the standard
weight. -/
theorem balancedWeight_eq_mul_standardZG (z : GameClause G → ℤ)
    (hbalance : ∀ player question, localBalanceG z player question = 0) :
    ∃ k : ℤ, z = fun c => k * standardZG c := by
  refine ⟨-z (0, false), ?_⟩
  funext c
  rcases c with ⟨g, b⟩
  cases b
  · have hz := balance_E_constant z hbalance g
    simp [standardZG]
    linarith
  · have hz := balance_O_eq_neg_E z hbalance g
    have hzE := balance_E_constant z hbalance g
    simp [standardZG]
    linarith

/-- The parity sum of an odd-multiple standard weight is exactly that
multiplier. -/
private lemma oddMul_standardZG_parity_sum (k : ℤ) :
    (∑ c : GameClause G, (k * standardZG c) * parityG c) = k := by
  have hO : (∑ g : G, k * parityG (g, true)) = k := by
    rw [Fintype.sum_eq_single (0 : G)]
    · simp
    · intro g hg
      simp [parityG_O_ne_zero hg]
  rw [Fintype.sum_prod_type]
  simp [hO]

/-- A PREF is exactly an odd scalar multiple of the standard weight. -/
theorem isPREFG_iff_exists_odd_mul_standardZG (z : GameClause G → ℤ) :
    IsPREFG z ↔ ∃ k : ℤ, Odd k ∧ z = fun c => k * standardZG c := by
  constructor
  · intro hpref
    rcases hpref with ⟨hbalance, hparity⟩
    rcases balancedWeight_eq_mul_standardZG z hbalance with ⟨k, hz⟩
    refine ⟨k, ?_, hz⟩
    have hpar' : k % 2 = 1 := by
      have hz' : (fun c : GameClause G => z c * parityG c) =
          fun c : GameClause G => (k * standardZG c) * parityG c := by
        funext c
        rw [hz]
      rw [hz'] at hparity
      rwa [oddMul_standardZG_parity_sum k] at hparity
    exact Int.odd_iff.mpr hpar'
  · rintro ⟨k, hodd, hz⟩
    subst z
    constructor
    · intro player question
      unfold localBalanceG
      have hstd : (∑ c : GameClause G,
          standardZG c * (if letterG c player = question then 1 else 0)) = 0 := by
        have hb := (standardZG_isPREF (G := G)).1 player question
        unfold localBalanceG at hb
        exact hb
      calc
        (∑ c : GameClause G,
            (k * standardZG c) * (if letterG c player = question then 1 else 0))
            = k * (∑ c : GameClause G,
                standardZG c * (if letterG c player = question then 1 else 0)) := by
                symm
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro c hc
                ring
        _ = 0 := by rw [hstd]; simp
    · rw [oddMul_standardZG_parity_sum k]
      exact Int.odd_iff.mp hodd

end FourXOR
end Research
end QIT

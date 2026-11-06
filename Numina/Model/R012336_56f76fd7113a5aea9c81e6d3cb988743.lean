import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_241989 {S : Set ℝ}
  (hS : S = {x | ∃ t : ℝ, t ≥ 0 ∧ x = (2 * t + 3) / (t + 2)}) :
  IsLeast {x | ∃ t : ℝ, t ≥ 0 ∧ x = (2 * t + 3) / (t + 2)} (3 / 2) ∧
  ¬ ∃ b : ℝ, IsGreatest {x | ∃ t : ℝ, t ≥ 0 ∧ x = (2 * t + 3) / (t + 2)} b := by
  constructor
  · -- Let's prove that 3/2 is the least of S
    constructor
    · -- Show 3/2 is in S
      use 0
      norm_num
    · -- Show for all x in S, 3/2 ≤ x
      intro x hx
      rcases hx with ⟨t, ht, hx⟩
      have h3 : (3 / 2 : ℝ) ≤ (2 * t + 3) / (t + 2) := by
        apply (le_div_iff₀ (by
          nlinarith)).mpr
        nlinarith
      rw [hx]
      linarith [h3]
  · -- Let's prove that there is no greatest element in S
    intro h
    rcases h with ⟨b, hb⟩
    rcases hb with ⟨hb1, hb2⟩
    rcases hb1 with ⟨t, ht, h1⟩
    have h2 : ∃ t' : ℝ, t' ≥ 0 ∧ ( (2 * t' + 3) / (t' + 2) > b ) := by
      use t + 1
      constructor
      · -- Show t + 1 ≥ 0
        nlinarith
      · -- Show (2 * (t + 1) + 3) / ((t + 1) + 2) > b
        have h3 : (2 * (t + 1) + 3) / ((t + 1) + 2) > b := by
          rw [h1]
          have h4 : (2 * (t + 1) + 3 : ℝ) / ((t + 1) + 2) - ( (2 * t + 3) / (t + 2) ) > 0 := by
            have h5 : (2 * (t + 1) + 3 : ℝ) / ((t + 1) + 2) - ( (2 * t + 3) / (t + 2) ) =
                ( (2 * (t + 1) + 3) * (t + 2) - (2 * t + 3) * ((t + 1) + 2) ) / ( ( (t + 1) + 2 ) * (t + 2) ) := by
              field_simp
              <;> ring
            rw [h5]
            have h6 : (2 * (t + 1) + 3 : ℝ) * (t + 2) - (2 * t + 3) * ( (t + 1) + 2 ) = (1 : ℝ) := by
              nlinarith
              <;> ring_nf <;> nlinarith
            rw [h6]
            have h7 : ( (t + 1 + 2 ) : ℝ ) * (t + 2) > (0 : ℝ ) := by
              positivity
            exact div_pos (by linarith) h7
          linarith
        linarith
    rcases h2 with ⟨t', ht', h2⟩
    have h3 : ( (2 * t' + 3 : ℝ ) / (t' + 2) ) ∈ {x | ∃ t : ℝ, t ≥ 0 ∧ x = (2 * t + 3) / (t + 2)} := by
      refine' ⟨t', ht', rfl⟩
    have h4 : ( (2 * t' + 3 : ℝ ) / (t' + 2) ) ≤ b := by
      apply hb2
      exact h3
    linarith
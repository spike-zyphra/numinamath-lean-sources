import Mathlib

open Real

theorem inequalities_144834 (n : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a + b = 2) :
    1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) ∧ (∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b = 2 ∧ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) = 1) := by
  have h1 : 1 ≤ 1 / (1 + a ^ n) + 1 / (1 + b ^ n) := by
    have h2 : 0 < (1 + a ^ n : ℝ) := by
      have h3 : 0 ≤ a ^ n := by positivity
      linarith
    have h3 : 0 < (1 + b ^ n : ℝ) := by
      have h4 : 0 ≤ b ^ n := by positivity
      linarith
    have h4 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) : ℝ) ≥ 1 := by
      have h5 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 : ℝ) ≥ 0 := by
        have h6 : 0 < (1 + a ^ n : ℝ) * (1 + b ^ n) := by
          positivity
        have h7 : (1 / (1 + a ^ n) + 1 / (1 + b ^ n) - 1 : ℝ) =
            ( (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ) / ( (1 + a ^ n) * (1 + b ^ n) ) := by
          field_simp [show (1 + (a : ℝ) ^ n) ≠ 0 by positivity, show (1 + (b : ℝ) ^ n) ≠ 0 by positivity]
          <;> ring
        rw [h7] at *
        apply div_nonneg
        have h8 : (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) ≥ 0 := by
          have h9 : (1 + b ^ n) + (1 + a ^ n) - (1 + a ^ n) * (1 + b ^ n) = 1 - (a ^ n * b ^ n) := by
            ring_nf
          rw [h9]
          have h10 : a ^ n * b ^ n ≤ (1 : ℝ) := by
            have h6 : a * b ≤ (1 : ℝ) := by
              nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), h]
            have h11 : a ^ n * b ^ n = (a * b) ^ n := by
              rw [mul_pow]
            rw [h11]
            have h12 : (a * b) ^ n ≤ (1 : ℝ) ^ n := by
              apply pow_le_pow_left
              all_goals nlinarith [h6, show 0 ≤ a * b by positivity, show 0 ≤ (1 : ℝ) by norm_num]
            have h13 : (1 : ℝ) ^ n = 1 := by
              norm_num
            nlinarith [h12, h13, h6]
          nlinarith
        all_goals positivity
      linarith
    linarith
  constructor
  · exact h1
  · use 1, 1
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    norm_num
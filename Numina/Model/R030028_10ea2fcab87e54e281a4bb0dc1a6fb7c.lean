import Mathlib

theorem algebra_5689 (x : ℝ) : 3^(x^2 - 5 * x) + (x^2 - 5 * x) / 3^x = 1 ↔ x = 0 ∨ x = 5 := by
  constructor
  · -- Forward implication: if equation holds then x=0 or x=5
    intro h_eq
    have h1 : (3 : ℝ) ^ (x ^ 2 - 5 * x) > 0 := by positivity
    have h2 : (3 : ℝ) ^ x > 0 := by positivity
    have h3 : x ^ 2 - 5 * x = 0 := by
      by_cases h4 : x ^ 2 - 5 * x > 0
      · -- Assume x^2 - 5 * x > 0
        have h5 : (3 : ℝ) ^ (x ^ 2 - 5 * x) > 1 := by
          have h6 : (3 : ℝ) ^ (x ^ 2 - 5 * x) > (3 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          norm_num at h6 ⊢
          linarith
        have h7 : (x ^ 2 - 5 * x) / (3 : ℝ) ^ x > 0 := by
          apply div_pos
          · -- Show x^2 -5 x > 0
            linarith
          · -- Show (3: ℝ) ^x>0
            positivity
        linarith
      by_cases h8 : x ^ 2 - 5 * x < 0
      · -- Assume x^2 - 5 * x < 0
        have h5 : (3 : ℝ) ^ (x ^ 2 - 5 * x) < 1 := by
          have h6 : (3 : ℝ) ^ (x ^ 2 - 5 * x) < (3 : ℝ) ^ (0 : ℝ) := by
            apply Real.rpow_lt_rpow_of_exponent_lt
            all_goals linarith
          norm_num at h6 ⊢
          linarith
        have h7 : (x ^ 2 - 5 * x) / (3 : ℝ) ^ x < 0 := by
          apply div_neg_of_neg_of_pos
          · -- Show x^2 -5 x < 0
            linarith
          · -- Show (3: ℝ) ^x>0
            positivity
        linarith
      linarith
    have h9 : x * (x - 5) = 0 := by
      ring_nf at h3 ⊢
      linarith
    cases' (mul_eq_zero.1 h9) with h10 h11
    · -- h10 : x = 0
      left
      linarith
    · -- h11 : x - 5 = 0
      right
      linarith
  · -- Backward direction: if x =0 or x=5 then equation holds
    rintro (h_eq | h_eq)
    · -- x = 0
      rw [show x = (0 : ℝ) by linarith [h_eq]]
      norm_num
    · -- x = 5
      rw [show x = (5 : ℝ) by linarith [h_eq]]
      norm_num
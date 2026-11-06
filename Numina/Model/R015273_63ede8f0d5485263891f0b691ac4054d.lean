import Mathlib

open Real

theorem algebra_278784 {x : ℝ} (hx : x > 0) :
    x ^ (logb 10 x) = x ^ 3 / 100 ↔ x = 10 ∨ x = 100 := by
  constructor
  · -- Forward direction: prove that if x^(logb 10 x) = x^3 / 100 and x > 0, then x = 10 or x = 100
    intro h_eq
    have h1 : logb 10 (x ^ (logb 10 x)) = logb 10 (x ^ 3 / 100) := by
      rw [h_eq]
    -- The left side simplifies to (logb 10 x) ^ 2 using logarithm power rule
    have h2 : logb 10 (x ^ (logb 10 x)) = (logb 10 x) ^ 2 := by
      rw [logb_rpow_eq_mul_logb_of_pos]
      all_goals nlinarith [hx]
    -- The right side simplifies to 3 * (logb 10 x) - 2 using logarithm division and power rules
    have h3 : logb 10 (x ^ 3 / 100) = 3 * (logb 10 x) - 2 := by
      have h4 : logb 10 (x ^ 3 / 100) = logb 10 (x ^ 3) - logb 10 100 := by
        rw [← logb_div (by positivity) (by positivity)]
      have h5 : logb 10 (x ^ 3) = 3 * (logb 10 x) := by
        simp [logb_pow]
      have h6 : logb 10 100 = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h4, h5, h6]
      all_goals linarith
    -- Substitute the simplified expressions into h1 to get the quadratic equation
    rw [h2, h3] at h1
    -- Solve the quadratic equation (logb 10 x)^2 - 3 * (logb 10 x) + 2 = 0, which factors to (logb 10 x - 1) * (logb 10 x - 2) = 0
    have h7 : (logb 10 x - 1) * (logb 10 x - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- Case where logb 10 x = 1, so x = 10
      have h10 : logb 10 x = 1 := by linarith
      have hx1 : x = (10 : ℝ) := by
        have h11 : x = (10 : ℝ) ^ (logb 10 x) := by
          field_simp [Real.rpow_logb, hx, show (10 : ℝ) > 1 by norm_num]
        rw [h11, h10]
        all_goals norm_num
      left
      exact hx1
    · -- Case where logb 10 x = 2, so x = 100
      have h10 : logb 10 x = 2 := by linarith
      have hx1 : x = (100 : ℝ) := by
        have h11 : x = (10 : ℝ) ^ (logb 10 x) := by
          field_simp [Real.rpow_logb, hx, show (10 : ℝ) > 1 by norm_num]
        rw [h11, h10]
        all_goals norm_num
      right
      exact hx1
  · -- Backward direction: prove that if x = 10 or x = 100, then x^(logb 10 x) = x^3 / 100
    rintro (hx | hx)
    · -- Case x = 10
      rw [hx]
      have h1 : logb 10 (10 : ℝ) = 1 := by norm_num [logb_eq_iff_rpow_eq]
      rw [h1]
      all_goals norm_num
    · -- Case x = 100
      rw [hx]
      have h1 : logb 10 (100 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      rw [h1]
      all_goals norm_num
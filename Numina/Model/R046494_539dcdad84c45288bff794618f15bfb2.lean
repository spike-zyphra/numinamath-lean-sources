import Mathlib

theorem algebra_2262 {x : ℝ} (hx : x^3 + x ≥ 0 ∧ x + 8 ≥ 0) : (x^3 + x)^(1/3) + x^3 = (x + 8)^(1/3) + 8 ↔ x = 2 := by
  constructor
  · -- Assume the equation holds, prove x = 2
    intro h_eq
    have h1 : x^3 + x ≥ 0 := hx.1
    have h2 : x + 8 ≥ 0 := hx.2
    by_cases h : x < 2
    · -- Assume x < 2
      have h3 : x^3 < 8 := by
        nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x - 2), sq_nonneg (x + 2)]
      have h4 : (x^3 + x)^(1/3 : ℝ) < (x + 8)^(1/3 : ℝ) := by
        have h5 : x^3 + x < x + 8 := by nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x - 2), sq_nonneg (x + 2)]
        have h6 : (x^3 + x)^(1/3 : ℝ) < (x + 8)^(1/3 : ℝ) := by
          apply Real.rpow_lt_rpow
          all_goals linarith
        linarith
      nlinarith [show (x^3 + x)^(1/3 : ℝ) - (x + 8)^(1/3 : ℝ) < 0 by linarith, h_eq]
    · -- x ≥ 2
      by_cases h' : x > 2
      · -- Assume x > 2
        have h3 : x^3 > 8 := by
          nlinarith [sq_pos_of_pos (show 0 < x - 2 by linarith), sq_nonneg (x^2 - 4), sq_nonneg (x - 2), sq_nonneg (x + 2)]
        have h4 : (x^3 + x)^(1/3 : ℝ) > (x + 8)^(1/3 : ℝ) := by
          have h5 : x^3 + x > x + 8 := by nlinarith [sq_pos_of_pos (show 0 < x - 2 by linarith), sq_nonneg (x^2 - 4)]
          have h6 : (x^3 + x)^(1/3 : ℝ) > (x + 8)^(1/3 : ℝ) := by
            apply Real.rpow_lt_rpow
            all_goals linarith
          linarith
        nlinarith [show (x^3 + x)^(1/3 : ℝ) - (x + 8)^(1/3 : ℝ) > 0 by linarith, h_eq]
      · -- x ≤ 2, so x = 2
        have h_eq2 : x = 2 := by linarith
        exact h_eq2
  · -- Assume x = 2, prove the equation
    intro h_eq
    rw [h_eq]
    have h3 : ( (2:ℝ)^3 + (2:ℝ) )^(1/3 : ℝ) = ( (2 + 8 : ℝ) )^(1/3 : ℝ) := by
      norm_num
    nlinarith [h3]
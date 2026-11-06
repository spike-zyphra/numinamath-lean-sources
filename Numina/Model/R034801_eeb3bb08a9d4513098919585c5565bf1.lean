import Mathlib

open Real Function


theorem algebra_164709 {x : ℝ} (h : 2^(x^2 - 2 * x) + 3^(x^2 - 2 * x) + x^2 - 2 * x + 1 / 6 = 0) : x = 1 := by
  have h1 : x ^ 2 - 2 * x = -1 := by 
    by_cases h2 : x ^ 2 - 2 * x < -1
    · -- Assume x^2 - 2 x < -1
      have h3 : x ^ 2 - 2 * x < -1 := h2
      have h4 : (2 : ℝ) ^ (x ^ 2 - 2 * x) < (1 / 2 : ℝ) := by
        have h5 : x ^ 2 - 2 * x < (-1 : ℝ) := h3
        have h6 : (2 : ℝ) ^ (x ^ 2 - 2 * x) < (2 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals nlinarith
        have h7 : (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) := by norm_num
        rw [h7] at h6 
        linarith
      have h5 : (3 : ℝ) ^ (x ^ 2 - 2 * x) < (1 / 3 : ℝ) := by
        have h8 : x ^ 2 - 2 * x < (-1 : ℝ) := h3
        have h9 : (3 : ℝ) ^ (x ^ 2 - 2 * x) < (3 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals nlinarith
        have h10 : (3 : ℝ) ^ (-1 : ℝ) = (1 / 3 : ℝ) := by norm_num
        rw [h10] at h9 
        linarith
      have h7 : (2 : ℝ) ^ (x ^ 2 - 2 * x) + (3 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) < (-1 / 6 : ℝ) := by
        nlinarith [show (0 : ℝ) < (2 : ℝ) by norm_num, show (0 : ℝ) < (3 : ℝ) by norm_num, 
          Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (x ^ 2 - 2 * x), 
          Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (x ^ 2 - 2 * x)
        ]
      have h8 : (2 : ℝ) ^ (x ^ 2 - 2 * x) + (3 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) + (1 / 6 : ℝ) < (0 : ℝ) := by 
        nlinarith 
      nlinarith
    by_cases h3 : x ^ 2 - 2 * x > -1
    · -- Assume x^2 - 2 x > -1
      have h4 : (2 : ℝ) ^ (x ^ 2 - 2 * x) > (1 / 2 : ℝ) := by
        have h8 : x ^ 2 - 2 * x > (-1 : ℝ) := by linarith
        have h9 : (2 : ℝ) ^ (x ^ 2 - 2 * x) > (2 : ℝ) ^ (-1 : ℝ) := by 
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith 
        have h10 : (2 : ℝ) ^ (-1 : ℝ) = (1 / 2 : ℝ) := by norm_num
        rw [h10] at h9
        linarith
      have h5 : (3 : ℝ) ^ (x ^ 2 - 2 * x) > (1 / 3 : ℝ) := by
        have h8 : x^2 - 2 * x > (-1 : ℝ) := by linarith
        have h9 : (3 : ℝ) ^ (x^2 - 2 * x) > (3 : ℝ) ^ (-1 : ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt
          all_goals linarith
        have h10 : (3 : ℝ) ^ (-1 : ℝ) = (1 / 3 : ℝ) := by norm_num
        rw [h10] at h9
        linarith
      have h7 : (2 : ℝ) ^ (x ^ 2 - 2 * x) + (3 : ℝ) ^ (x ^ 2 - 2 * x) + (x ^ 2 - 2 * x) > (-1 / 6 : ℝ) := by
        nlinarith [show (0 : ℝ) < (2 : ℝ) by norm_num, show (0 : ℝ) < (3 : ℝ) by norm_num, 
          Real.rpow_pos_of_pos (show (0 : ℝ) < (2 : ℝ) by norm_num) (x ^ 2 - 2 * x), 
          Real.rpow_pos_of_pos (show (0 : ℝ) < (3 : ℝ) by norm_num) (x ^ 2 - 2 * x)
        ]
      have h8 : (2 : ℝ) ^ (x^2 - 2 * x) + (3 : ℝ) ^ (x^2 - 2 * x) + (x ^ 2 - 2 * x) + (1 / 6 : ℝ) > (0 : ℝ) := by 
        nlinarith 
      nlinarith
    linarith
  have h2 : (x - 1) ^ 2 = 0 := by
    nlinarith
  have h3 : x - 1 = 0 := by
    rw [sq_eq_zero_iff] at h2
    exact h2
  linarith
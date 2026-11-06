import Mathlib

theorem algebra_185455 {x : ℝ} (hx : 0 ≤ x) :
    2021 * x ^ ((2020 : ℝ) / 202) - 1 = 2020 * x ↔ x = 1 := by
  constructor
  · -- Assume the equation holds, prove x = 1
    intro h_eq
    have h1 : x ^ ((2020 : ℝ) / 202) = x ^ (10 : ℝ) := by
      norm_num
    rw [h1] at h_eq
    have h4 : x ^ (10 : ℝ) = x ^ 10 := by
      norm_cast
    rw [h4] at h_eq
    have h2 : (2021 : ℝ) * (x ^ 10) - 2020 * x - 1 = 0 := by 
      nlinarith
    have h3 : x ≥ 0 := by linarith
    have h6 : x = 1 := by
      nlinarith [sq_nonneg (x ^ 5 - 1), sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 3 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg (x - 1), 
        sq_nonneg (x ^ 5), sq_nonneg (x ^ 4), sq_nonneg (x ^ 3), sq_nonneg (x ^ 2), sq_nonneg (x),
          pow_nonneg (show (0 : ℝ) ≤ x by linarith) 2, pow_nonneg (show (0 : ℝ) ≤ x by linarith) 3, pow_nonneg (show (0 : ℝ) ≤ x by linarith) 4, pow_nonneg (show (0 : ℝ) ≤ x by linarith) 5, pow_nonneg (show (0 : ℝ) ≤ x by linarith) 10
        ]
    assumption
  · -- Assume x = 1, prove the equation
    intro h_eq
    rw [h_eq]
    norm_num
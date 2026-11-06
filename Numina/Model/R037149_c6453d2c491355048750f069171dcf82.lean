import Mathlib

open Real

theorem algebra_186654 {x : ℝ} (hx : 0 < x) :
    logb 3 (x + 2) * logb 3 (2 * x + 1) * (3 - logb 3 (2 * x ^ 2 + 5 * x + 2)) = 1 ↔ x = 1 := by
  constructor
  · -- Assume the equation holds, prove x = 1
    intro h_eq
    have h1 : 2 * x ^ 2 + 5 * x + 2 = (x + 2) * (2 * x + 1) := by
      ring
    have h2 : logb 3 (2 * x ^ 2 + 5 * x + 2) = logb 3 (x + 2) + logb 3 (2 * x + 1) := by
      have h1' : 2 * x ^ 2 + 5 * x + 2 = (x + 2) * (2 * x + 1) := by
        ring
      have h3 : x + 2 > 0 := by linarith
      have h4 : 2 * x + 1 > 0 := by linarith
      rw [h1']
      rw [logb_mul (by positivity) (by positivity)]
    rw [h2] at h_eq
    have ha1 : logb 3 (x + 2) > 0 := by
      have h3 : x + 2 > 1 := by linarith
      have h4 : logb 3 (x + 2) > 0 := by
        apply logb_pos
        all_goals
          linarith
      linarith
    have ha2 : logb 3 (2 * x + 1) > 0 := by
      have h5 : 2 * x + 1 > 1 := by linarith
      have h6 : logb 3 (2 * x + 1) > 0 := by
        apply logb_pos
        all_goals
          linarith
      linarith
    have h3 : (logb 3 (x + 2) - 1) ^ 2 + (logb 3 (2 * x + 1) - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (logb 3 (x + 2) - 1), sq_nonneg (logb 3 (2 * x + 1) - 1),
          sq_nonneg (logb 3 (x + 2) * logb 3 (2 * x + 1) - 1), 
          sq_nonneg (logb 3 (x + 2) + logb 3 (2 * x + 1) - 2), 
          mul_pos ha1 ha2, 
          sq_nonneg (logb 3 (x + 2) - logb 3 (2 * x + 1)), 
          sq_nonneg (logb 3 (x + 2) + logb 3 (2 * x + 1) - 2), 
          mul_nonneg (show 0 ≤ (logb 3 (x + 2) : ℝ) by linarith) 
             (show 0 ≤ (logb 3 (2 * x + 1) : ℝ) by linarith)
          ]
    have ha3 : logb 3 (x + 2) - 1 = 0 := by
      nlinarith [sq_nonneg (logb 3 (x + 2) - 1), sq_nonneg (logb 3 (2 * x + 1) - 1)]
    have ha4 : logb 3 (2 * x + 1) - 1 = 0 := by
      nlinarith [sq_nonneg (logb 3 (x + 2) - 1), sq_nonneg (logb 3 (2 * x + 1) - 1)]
    have ha5 : logb 3 (x + 2) = 1 := by linarith
    have ha6 : logb 3 (2 * x + 1) = 1 := by linarith
    have ha7 : x + 2 = 3 := by
      have h3 : logb 3 (x + 2) = 1 := ha5
      rw [logb_eq_iff_rpow_eq] at h3
      · -- If the logarithm equals 1, then the argument equals 3^1 = 3
        nlinarith
      all_goals
        linarith
    have ha8 : 2 * x + 1 = 3 := by
      have h4 : logb 3 (2 * x + 1) = 1 := ha6
      rw [logb_eq_iff_rpow_eq] at h4
      · -- If the logarithm equals 1, then the argument equals 3^1 = 3
        nlinarith
      all_goals
        nlinarith
    -- Solving the linear equations
    linarith
  · -- Assume x = 1, prove the equation holds
    intro h_eq
    rw [show x = 1 by linarith [h_eq]]
    have h1 : logb 3 (1 + 2) = 1 := by
      rw [show (1 + 2 : ℝ) = (3 : ℝ) by norm_num]
      have h2 : logb 3 (3 : ℝ) = 1 := by
        rw [logb_self_eq_one]
        all_goals
          norm_num
      linarith
    have h2 : logb 3 (2 * (1 : ℝ) + 1) = 1 := by
      rw [show (2 * (1 : ℝ) + 1 : ℝ) = (3 : ℝ) by norm_num]
      have h3 : logb 3 (3 : ℝ) = 1 := by
        rw [logb_self_eq_one]
        all_goals
          norm_num
      linarith
    have h3 : logb 3 (2 * (1 : ℝ) ^ 2 + 5 * (1 : ℝ) + 2) = 2 := by
      rw [show (2 * (1 : ℝ) ^ 2 + 5 * (1 : ℝ) + 2 : ℝ) = (9 : ℝ) by norm_num]
      have h4 : logb 3 (9 : ℝ) = 2 := by
        rw [logb_eq_iff_rpow_eq] <;> norm_num
      linarith
    rw [h1, h2, h3]
    all_goals
      norm_num
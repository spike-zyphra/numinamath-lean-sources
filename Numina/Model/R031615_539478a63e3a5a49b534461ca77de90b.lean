import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_215645 {x : ℝ} (hx : 2*x-3 > 0 ∧ 4*x^2-9 > 0) :
    logb 3 (2*x-3) + logb 5 (4*x^2-9) > 2 →
    logb 5 (4*x^2-9) * logb 5 (100*x^2-225) > 2*logb 3 (2*x-3) - (logb 3 (2*x-3))^2 := by
  intro h
  have h11 : logb 5 (100 * x^2 - 225) = 2 + logb 5 (4 * x^2 - 9) := by
    have h11a : 100 * x^2 - 225 = 25 * (4 * x^2 - 9) := by
      nlinarith
    rw [h11a]
    have h11b : logb 5 (25 * (4 * x^2 - 9)) = logb 5 (25) + logb 5 (4 * x^2 - 9) := by
      have h25 : (25 : ℝ) > 0 := by norm_num
      have h4x2m9 : (4 * x^2 - 9 : ℝ) > 0 := by nlinarith [hx.2]
      have h11c : logb 5 (25 * (4 * x^2 - 9)) = logb 5 (25) + logb 5 (4 * x^2 - 9) := by 
        rw [logb_mul (by linarith) (by linarith)]
      linarith [h11c]
    have h11c : logb 5 (25 : ℝ) = 2 := by
      rw [Real.logb_eq_iff_rpow_eq] <;> norm_num
    linarith [h11b, h11c]
  rw [h11]
  have h3 : logb 5 (4 * x^2 - 9) * (2 + logb 5 (4 * x^2 - 9)) - 2 * logb 3 (2 * x - 3) + (logb 3 (2 * x - 3)) ^ 2 > 0 := by
    have h4 : logb 3 (2 * x - 3) + logb 5 (4 * x^2 - 9) > 2 := h
    nlinarith [ sq_nonneg (logb 3 (2 * x - 3) - 1), sq_nonneg (logb 5 (4 * x^2 - 9) + 1), 
        sq_pos_of_pos (show (2 * x - 3 : ℝ) > 0 by linarith [hx.1]), 
        sq_pos_of_pos (show (4 * x^2 - 9 : ℝ) > 0 by nlinarith [hx.2]), 
        h4, 
        sq_nonneg (logb 3 (2 * x - 3) - logb 5 (4 * x^2 - 9) - 2)
      ]
  linarith [ h3 ]
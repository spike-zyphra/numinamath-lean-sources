import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_215645 {x : ℝ} (hx : 2*x-3 > 0 ∧ 4*x^2-9 > 0) :
    logb 3 (2*x-3) + logb 5 (4*x^2-9) > 2 →
    logb 5 (4*x^2-9) * logb 5 (100*x^2-225) > 2*logb 3 (2*x-3) - (logb 3 (2*x-3))^2 := by
  intro h1
  -- 2*x−3>0 and 4*x^2−9>0 from the problem statement.
  have h2 : 4 * x^2 - 9 > 0 := hx.right
  have h3 : 2 * x - 3 > 0 := hx.left
  have h4 : logb 5 (100 * x^2 - 225) = logb 5 (25 * (4 * x^2 - 9)) := by
    ring_nf
  have h5 : logb 5 (25 * (4 * x^2 - 9)) = logb 5 25 + logb 5 (4 * x^2 - 9) := by
    rw [logb_mul (by nlinarith) (by nlinarith)]
  have h6 : logb 5 (25 : ℝ) = 2 := by
    rw [logb_eq_iff_rpow_eq] <;> norm_num
  have h7 : logb 5 (100 * x^2 - 225) = 2 + logb 5 (4 * x^2 - 9) := by
    rw [h4, h5, h6]
  have h8 : logb 5 (4 * x^2 - 9) * logb 5 (100 * x^2 - 225) = 
            logb 5 (4 * x^2 - 9) * (2 + logb 5 (4 * x^2 - 9)) := by
    rw [h7]
  rw [h8]
  nlinarith [sq_nonneg (logb 3 (2 * x - 3) - 1), sq_nonneg (logb 5 (4 * x^2 - 9) + 1),
    sq_nonneg (logb 3 (2 * x - 3) - 2), sq_nonneg (logb 5 (4 * x^2 - 9)), h1]
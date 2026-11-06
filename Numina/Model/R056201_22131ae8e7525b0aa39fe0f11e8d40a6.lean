import Mathlib

theorem inequalities_325857 (x y z : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) (hy : 0 ≤ y ∧ y ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) :
    x * y * z + (1 - x) * (1 - y) * (1 - z) ≤ 1 := by
  nlinarith [mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith), 
          mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ y by linarith) (show 0 ≤ z by linarith), 
          mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - y by linarith), 
          mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ 1 - z by linarith), 
          mul_nonneg (show 0 ≤ 1 - y by linarith) (show 0 ≤ 1 - z by linarith), 
          mul_nonneg (mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ y by linarith)) (show 0 ≤ z by linarith), 
          mul_nonneg (mul_nonneg (show 0 ≤ x by linarith) (show 0 ≤ 1 - y by linarith)) (show 0 ≤ 1 - z by linarith),
          mul_nonneg (mul_nonneg (show 0 ≤ 1 - x by linarith) (show 0 ≤ y by linarith)) (show 0 ≤ 1 - z by linarith),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x - 0), sq_nonneg (y - 0), sq_nonneg (z - 0),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1)]
  all_goals nlinarith
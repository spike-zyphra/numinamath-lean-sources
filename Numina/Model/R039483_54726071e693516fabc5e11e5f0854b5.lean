import Mathlib

theorem inequalities_317724 (x y z : ℝ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    (x^2 - 2 * x + 2) * (y^2 - 2 * y + 2) * (z^2 - 2 * z + 2) ≤ (x * y * z)^2 - 2 * x * y * z + 2 := by

  have hx1 : 0 ≤ x - 1 := by linarith
  have hy1 : 0 ≤ y - 1 := by linarith
  have hz1 : 0 ≤ z - 1 := by linarith
  nlinarith [sq_nonneg (x * y - 1), sq_nonneg (y * z - 1), sq_nonneg (z * x - 1),
          sq_nonneg (x - 1), sq_nonneg (y - 1), sq_nonneg (z - 1),
          sq_nonneg (x * y * z - 1),
          mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ y - 1 by linarith),
          mul_nonneg (show 0 ≤ y - 1 by linarith) (show 0 ≤ z - 1 by linarith),
          mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ z - 1 by linarith),
          mul_nonneg (mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ y - 1 by linarith)) (show 0 ≤ z - 1 by linarith),
          mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ y - 1 by linarith),
          mul_nonneg (show 0 ≤ x by nlinarith) (show 0 ≤ z - 1 by linarith),
          mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ x - 1 by linarith),
          mul_nonneg (show 0 ≤ y by nlinarith) (show 0 ≤ z - 1 by linarith),
          mul_nonneg (show 0 ≤ z by nlinarith) (show 0 ≤ x - 1 by linarith),
          mul_nonneg (show 0 ≤ z by nlinarith) (show 0 ≤ y - 1 by linarith),
          mul_nonneg (show 0 ≤ x - 1 by linarith) (show 0 ≤ y * z - 1 by nlinarith),
          mul_nonneg (show 0 ≤ y - 1 by linarith) (show 0 ≤ x * z - 1 by nlinarith),
          mul_nonneg (show 0 ≤ z - 1 by linarith) (show 0 ≤ x * y - 1 by nlinarith)
      ]
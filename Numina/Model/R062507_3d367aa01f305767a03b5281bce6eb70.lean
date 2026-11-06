import Mathlib

theorem algebra_273068 {x y z w : ℝ}
    (h1 : x = 6 * y) (h2 : 3 * y = 4 * z) (h3 : 2 * z = 6 * w) :
    2 * x = 48 * w := by
  have hz : z = 3 * w := by
    linarith
  have hy : y = 4 * w := by
    rw [hz] at h2
    linarith
  rw [show x = 6 * y by linarith [h1]]
  rw [hy]
  linarith
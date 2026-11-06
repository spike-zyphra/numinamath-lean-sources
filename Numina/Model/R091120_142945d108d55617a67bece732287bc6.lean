import Mathlib

theorem algebra_298303 (x y z : ℝ) (h1 : 2 * x + 3 * y + z = 13) (h2 : 4 * x ^ 2 + 9 * y ^ 2 + z ^ 2 - 2 * x + 15 * y + 3 * z = 82) :
    (x, y, z) = (3, 1, 4) := by
  have h3 : z = 13 - 2 * x - 3 * y := by 
    linarith
  rw [h3] at h2
  have eq1 : (y - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 1), sq_nonneg (2 * x + 3 * y - 13)]
  have eq2 : y - 1 = 0 := by 
    nlinarith [eq1]
  have hy : y = 1 := by linarith
  have hx : x = 3 := by
    nlinarith [hy, h1, h2]
  have hz : z = 4 := by
    rw [hx, hy] at h1
    linarith
  simp [hx, hy, hz]
import Mathlib

theorem algebra_289658 (x y z : ℝ) (h1 : x * y + y * z + z * x = 1) (h2 : 5 * x + 8 * y + 9 * z = 12) :
    (x, y, z) = (1, 1 / 2, 1 / 3) := by
  have h3 : z = (12 - 5 * x - 8 * y) / 9 := by
    linarith
  rw [h3] at h1
  have hx1 : (x - 1) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x - 1), sq_nonneg (y - 1 / 2), sq_nonneg ((12 - 5 * x - 8 * y) / 9 - 1 / 3)]
  have hx2 : x - 1 = 0 := by
    apply pow_eq_zero 
    exact hx1
  have hx3 : x = 1 := by linarith
  have hx4 : y = 1 / 2 := by
    rw [hx3] at h1
    nlinarith [sq_nonneg (y - 1 / 2), sq_nonneg ((12 - 5 * x - 8 * y) / 9 - 1 / 3)]
  have hx5 : z = 1 / 3 := by
    rw [hx3, hx4] at h2
    linarith
  simp [Prod.ext_iff, hx3, hx4, hx5]
  all_goals tauto
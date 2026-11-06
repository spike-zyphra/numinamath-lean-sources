import Mathlib

theorem algebra_108 {x y z : ℝ} (h₀ : x + y = 4) (h₁ : |z + 1| = x * y + 2 * y - 9) :
    x + 2 * y + 3 * z = 4 := by 
  have hx : x = 4 - y := by linarith
  rw [show x = 4 - y by linarith] at h₁
  have h2 : (y - 3) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h3 : |z + 1| ≥ 0 := by
    apply abs_nonneg
  have h4 : (4 - y) * y + 2 * y - 9 ≤ 0 := by
    nlinarith [sq_nonneg (y - 3)]
  have h5 : |z + 1| = 0 := by
    nlinarith [abs_nonneg (z + 1), h4, h₁]
  have hz : z + 1 = 0 := by
    rwa [abs_eq_zero] at h5
  have hz2 : z = -1 := by linarith
  have h6 : (y - 3) ^ 2 = 0 := by
    nlinarith [h5, sq_nonneg (y - 3), abs_nonneg (z + 1)]
  have hy : y = 3 := by
    rw [sq_eq_zero_iff] at h6
    linarith
  have hx2 : x = 1 := by 
    linarith [h₀, hy]
  rw [hx2, hy, hz2]
  norm_num
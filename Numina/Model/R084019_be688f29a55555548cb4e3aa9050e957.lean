import Mathlib

theorem algebra_312835 (x y z : ℝ) (h₀ : x + y = 4) (h₁ : abs (z + 1) = x * y + 2 * y - 9) :
    x + 2 * y + 3 * z = 4 := by
  have hx : x = 4 - y := by linarith
  rw [hx] at h₁
  have eq1 : abs (z + 1) = 6 * y - y^2 - 9 := by
    nlinarith
  have h2 : 6 * y - y^2 - 9 ≥ 0 := by
    nlinarith [abs_nonneg (z + 1)]
  have h3 : (y - 3)^2 ≤ 0 := by
    nlinarith
  have hy : y = 3 := by
    nlinarith [sq_nonneg (y - 3)]
  have hx' : x = 1 := by
    linarith [h₀, hy]
  have h4 : abs (z + 1) = 0 := by
    rw [hy] at h₁
    nlinarith
  have h5 : z + 1 = 0 := by
    rwa [abs_eq_zero] at h4
  have hz : z = -1 := by
    linarith
  rw [hx', hy, hz]
  norm_num
import Mathlib

theorem algebra_3795 {x y : ℝ} (h : x ^ 2 + x * y + y ^ 2 + 3 * y + 3 = 0) :
    (x, y) = (1, -2) := by
  have h1 : (x + y / 2) ^ 2 + 3 / 4 * (y + 2) ^ 2 = 0 := by
    nlinarith [h]
  have h2 : (x + y / 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + y / 2), sq_nonneg (y + 2)]
  have h3 : (y + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x + y / 2), sq_nonneg (y + 2)]
  have h4 : x + y / 2 = 0 := by
    rwa [sq_eq_zero_iff] at h2
  have h5 : y + 2 = 0 := by
    rwa [sq_eq_zero_iff] at h3
  have hy : y = -2 := by linarith
  have hx : x = 1 := by 
    rw [hy] at h4
    linarith
  simp [hx, hy]
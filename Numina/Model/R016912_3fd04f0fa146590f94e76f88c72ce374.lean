import Mathlib

theorem algebra_235223 {x y : ℝ} (h1 : x * y + x = 15) (h2 : x ^ 2 + y ^ 2 + x * y + y = 41) :
    (x, y) = (3, 4) ∨ (x, y) = (5, 2) := by
  have h3 : (x - 3) * (x - 5) = 0 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 5), sq_nonneg (y - 4), sq_nonneg (y - 2),
      sq_nonneg (x - y), sq_nonneg (x * (y - 4)), sq_nonneg ((y - 4) * (x - 3))]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case h4 : x - 3 = 0, so x = 3, which implies y = 4
    have hx : x = 3 := by linarith
    have hy : y = 4 := by
      rw [hx] at h1
      linarith
    left
    simp [hx, hy]
  · -- Case h5 : x - 5 = 0, so x = 5, which implies y = 2
    have hx : x = 5 := by linarith
    have hy : y = 2 := by
      rw [hx] at h1
      linarith
    right
    simp [hx, hy]
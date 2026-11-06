import Mathlib

theorem algebra_326767 {x y z : ℝ} (h₀ : x + y = 5) (h₁ : z ^ 2 = x * y + y - 9) :
    x + 2 * y + 3 * z = 8 := by
  have hy : y = 5 - x := by linarith
  rw [hy] at h₁
  have h2 : z ^ 2 + (x - 2) ^ 2 = 0 := by
    nlinarith
  have h3 : z ^ 2 = 0 := by
    linarith [sq_nonneg (z), sq_nonneg (x - 2)]
  have h4 : (x - 2) ^ 2 = 0 := by
    linarith [sq_nonneg (z), sq_nonneg (x - 2)]
  have hx : x = 2 := by
    nlinarith
  have hz : z = 0 := by
    nlinarith
  have hy' : y = 3 := by
    linarith [h₀, hx]
  rw [hx, hy', hz]
  norm_num
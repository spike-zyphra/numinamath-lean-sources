import Mathlib

theorem algebra_290425 {t : ℝ} (ht : t = 3) (x : ℝ)
    (h1 : x^2 - t * x + 36 = 0) (h2 : x^2 - 8 * x + t = 0) :
    x = 3 := by
  rw [ht] at h1 h2
  nlinarith [sq_nonneg (x - 3), sq_nonneg (x * x), sq_nonneg (x - 4), sq_nonneg (x * x - 4)]
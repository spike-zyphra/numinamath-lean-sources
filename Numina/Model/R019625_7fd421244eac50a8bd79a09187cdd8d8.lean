import Mathlib

theorem algebra_13445 (t : ℝ) (a b : ℝ) (h : a + b = t) :
    a^2 + b^2 ≥ t^2 / 2 := by
  have hb : b = t - a := by linarith 
  rw [hb]
  have eq1 : a ^ 2 + (t - a) ^ 2 = 2 * (a - t / 2) ^ 2 + t ^ 2 / 2 := by
    nlinarith 
  have h3 : 2 * (a - t / 2) ^ 2 ≥ 0 := by
    nlinarith [sq_nonneg (a - t / 2)]
  linarith [eq1, h3]
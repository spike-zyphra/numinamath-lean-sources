import Mathlib

theorem algebra_170801 (f : ℝ → ℝ) (a b : ℝ)
    (hf : ∀ x, f x = x ^ 3 - 6 * x ^ 2 + 17 * x - 5)
    (ha : f a = 3) (hb : f b = 23) : a + b = 4 := by
  have ha_eq : f a = a ^ 3 - 6 * a ^ 2 + 17 * a - 5 := hf a
  have hb_eq : f b = b ^ 3 - 6 * b ^ 2 + 17 * b - 5 := hf b
  rw [ha_eq] at ha
  rw [hb_eq] at hb
  have eq_a : a^3 - 6 * a^2 + 17 * a - 8 = 0 := by linarith
  have eq_b : b^3 - 6 * b^2 + 17 * b - 28 = 0 := by linarith
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 4), sq_nonneg (a - 2), sq_nonneg (b - 2)]
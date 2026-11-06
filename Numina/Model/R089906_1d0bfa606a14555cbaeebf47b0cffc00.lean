import Mathlib

theorem algebra_315406 {f : ℝ → ℝ} (hf : ∀ x, f x = x^3 + 3 * x^2 + 6 * x + 14)
    (a b : ℝ) (ha : f a = 1) (hb : f b = 19) : a + b = -2 := by
  have h1 : a^3 + 3 * a^2 + 6 * a + 13 = 0 := by
    rw [hf a] at ha
    nlinarith
  have h4 : b^3 + 3 * b^2 + 6 * b - 5 = 0 := by
    rw [hf b] at hb
    nlinarith
  have h5 : (a + b + 2) ^ 2 = 0 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a^2 - b^2), sq_nonneg (a+1), sq_nonneg (b+1), sq_nonneg (a - b + 2), sq_nonneg (a * b + a + b + 2), sq_nonneg (a * b)]
  have h6 : (a + b + 2) = 0 := by
    rw [sq_eq_zero_iff] at h5
    linarith
  linarith
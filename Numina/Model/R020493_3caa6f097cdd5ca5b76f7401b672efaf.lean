import Mathlib

theorem algebra_304346 {a b c x y : ℝ} (h₀ : a * x + b * y - 2 * c = 0) (h₁ : a * b - c^2 > 0) :
    x * y ≤ 1 := by
  have h2 : c = (a * x + b * y) / 2 := by
    linarith
  rw [h2] at h₁
  nlinarith [sq_nonneg (a * x - b * y), sq_nonneg (x - y), sq_nonneg (a - b), sq_nonneg (x * y - 1), sq_nonneg (x * a - y * b)]
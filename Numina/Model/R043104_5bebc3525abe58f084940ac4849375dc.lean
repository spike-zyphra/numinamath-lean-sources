import Mathlib

theorem inequalities_597501 (a b c x y z : ℝ)
    (h₀ : 0 ≤ c + z) (h₁ : c + z ≤ b + y) (h₂ : b + y ≤ a + x)
    (h₃ : a + b + c = x + y + z) :
    a * y + b * x ≥ a * c + x * z := by
  nlinarith [sq_nonneg (y - c), sq_nonneg (x - z), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (c - x), sq_nonneg (a - x), sq_nonneg (b - z), sq_nonneg (a - c), sq_nonneg (a + b + c - (x + y + z)), mul_nonneg (show (0 : ℝ) ≤ b + y - c - z by linarith) (show (0 : ℝ) ≤ a + x - b - y by linarith)]
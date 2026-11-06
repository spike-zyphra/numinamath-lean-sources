import Mathlib

theorem algebra_325735 (a b x y : ℝ) (h₀ : a + b = 2) (h₁ : x + y = 2) (h₂ : a * x + b * y = 5) :
    (a ^ 2 + b ^ 2) * x * y + a * b * (x ^ 2 + y ^ 2) = -5 := by
  have h3 : b = 2 - a := by linarith
  have h4 : y = 2 - x := by linarith
  rw [h3, h4] at h₂ ⊢
  ring_nf at h₂ ⊢
  nlinarith [sq_nonneg (a - 1), sq_nonneg (x - 1), sq_nonneg (a - x), sq_nonneg ((2 - a) - (2 - x))]
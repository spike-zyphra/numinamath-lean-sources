import Mathlib

theorem algebra_16996 {a b c : ℝ} (h₀ : a + b + c = 11) (h₁ : a * b + a * c + b * c = 25) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 506 := by
  have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c =
    (a + b + c) * ((a + b + c) ^ 2 - 3 * (a * b + a * c + b * c)) := by
    ring
  rw [h2, h₀, h₁]
  norm_num
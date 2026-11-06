import Mathlib

theorem algebra_209463 {a b c x y : ℝ} (h₀ : a = x - y) (h₁ : b = x ^ 2 - y ^ 2)
    (h₂ : c = x ^ 3 - y ^ 3) :
    a ^ 4 + 3 * b ^ 2 - 4 * a * c = 0 := by 
  rw [h₀, h₁, h₂]
  ring
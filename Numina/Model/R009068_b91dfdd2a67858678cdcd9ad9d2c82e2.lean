import Mathlib

theorem algebra_13096 {a b c : ℝ} (h₀ : a + b + c = 1) (h₁ : a * b + a * c + b * c = -4)
    (h₂ : a * b * c = -4) :
    a ^ 3 + b ^ 3 + c ^ 3 = 1 := by

  have h3 : a^3 + b^3 + c^3 = (a + b + c)^3 - 3 * (a + b + c) * (a * b + a * c + b * c) + 3 * (a * b * c) := by 
    ring

  rw [h3, h₀, h₁, h₂]

  norm_num
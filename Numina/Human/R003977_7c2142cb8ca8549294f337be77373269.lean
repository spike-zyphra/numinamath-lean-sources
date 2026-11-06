import Mathlib

theorem algebra_226447 {a b c : ℝ} (h₀ : a + b + c = 0) (h₁ : a * b * c = 4) :
    a ^ 3 + b ^ 3 + c ^ 3 = 12 := by
  have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 0 := by
    have h2 : a ^ 3 + b ^ 3 + c ^ 3 - 3 * (a * b * c) = 
        (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2 - (a * b + b * c + c * a)) := by ring
    rw [h₀] at h2
    linarith
  linarith [h₁, h2]
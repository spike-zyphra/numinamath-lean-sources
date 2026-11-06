import Mathlib

theorem algebra_20836 {a c : ℝ} (f : ℝ → ℝ) (h₀ : ∀ x, f x = x ^ 7 + a * x ^ 3 + c * x)
    (h₁ : f 5 = 3) : f (-5) = -3 := by
  have h2 : f 5 = 5 ^ 7 + a * 5 ^ 3 + c * 5 := h₀ 5
  have h3 : f (-5) = (-5) ^ 7 + a * (-5) ^ 3 + c * (-5) := h₀ (-5)
  rw [h2] at h₁
  rw [h3]
  have h4 : (-5 : ℝ) ^ 7 + a * (-5 : ℝ) ^ 3 + c * (-5 : ℝ) = - (5 ^ 7 + a * 5 ^ 3 + c * 5) := by 
    ring_nf
    <;> ring_nf
  rw [h4]
  linarith
import Mathlib

theorem algebra_4941 {p q : ℝ} (h₀ : p * q = 9) (h₁ : p + q = 6) : p^2 + q^2 = 18 := by
  have h2 : p^2 + q^2 = (p + q)^2 - 2 * (p * q) := by 
    ring
  rw [h2, h₀, h₁]
  norm_num
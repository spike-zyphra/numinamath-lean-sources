import Mathlib

  theorem algebra_302945 {x y z : ℝ} (h₁ : x = 6 - y) (h₂ : z^2 = x * y - 9) : x = y := by
    rw [h₁] at h₂
    have h3 : z^2 = (6 - y) * y - 9 := h₂
    have h4 : (y - 3) ^ 2 + z^2 = 0 := by 
      linarith
    have hy : (y - 3) ^ 2 = 0 := by 
      linarith [sq_nonneg (y - 3), sq_nonneg z]
    have y_eq : y = 3 := by 
      linarith [pow_eq_zero hy]
    have x_eq : x = 3 := by 
      rw [h₁, y_eq]
      linarith
    linarith
import Mathlib

theorem algebra_9444 {x y m : ℝ} (h₀ : 4 * x + 2 * y = 3 * m) (h₁ : 3 * x + y = m + 2)
    (h₂ : y = -x) : m = 1 := by 
  rw [h₂] at h₀ h₁ 
  linarith
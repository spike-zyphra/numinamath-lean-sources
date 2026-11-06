import Mathlib

/- Given that $x + y = 3$ and $x - y = 4$, find $2x^2 + 2y^2$. -/
theorem algebra_21206 {x y : ℝ} (h₀ : x + y = 3) (h₁ : x - y = 4) :
    2 * x ^ 2 + 2 * y ^ 2 = 25 := by 
  have h₂ : x = 3 - y := by linarith
  rw [h₂] at h₀ h₁
  nlinarith
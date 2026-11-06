import Mathlib

/- If $x + 2y= 4$ and $xy = -8$, what is the value of $x^2 + 4y^2$? -/
theorem algebra_15589 {x y : ℝ} (h₀ : x + 2 * y = 4) (h₁ : x * y = -8) :
    x ^ 2 + 4 * y ^ 2 = 48 := by 
  nlinarith [sq_nonneg (x + 2 * y)]
import Mathlib

/- If $(x + y)^2 = 45$ and $xy = 10$, what is $(x - y)^2$? -/
theorem algebra_10722 {x y : ℝ} (h₀ : (x + y) ^ 2 = 45) (h₁ : x * y = 10) :
    (x - y) ^ 2 = 5 := by 
  nlinarith
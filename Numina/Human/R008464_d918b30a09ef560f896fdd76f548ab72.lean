import Mathlib

/- If $x+y=9$ and $xy=10$, what is the value of $x^3+y^3$? -/
theorem algebra_14923 {x y : ℝ} (h₀ : x + y = 9) (h₁ : x * y = 10) :
    x ^ 3 + y ^ 3 = 459 := by
  linear_combination (x ^ 2 - 1 * x * y + y ^ 2 + 9 * x + 9 * y + 81) * h₀ - 27 * h₁

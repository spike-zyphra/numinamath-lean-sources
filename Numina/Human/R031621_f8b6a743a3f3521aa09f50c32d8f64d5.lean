import Mathlib

/- If $3a + b + c = -3, a+3b+c = 9, a+b+3c = 19$, then find $abc$. -/
theorem algebra_21418 {a b c : ℝ} (h₀ : 3 * a + b + c = -3) (h₁ : a + 3 * b + c = 9)
    (h₂ : a + b + 3 * c = 19) : a * b * c = -56 := by 
  nlinarith [sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
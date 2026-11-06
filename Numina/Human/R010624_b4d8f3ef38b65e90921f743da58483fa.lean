import Mathlib

/- If $a + b + c = 11$ and $ab + ac + bc = 25,$ then find
\[a^3 + b^3 + c^3 - 3abc.\] -/
theorem algebra_16996 {a b c : ℝ} (h₀ : a + b + c = 11) (h₁ : a * b + a * c + b * c = 25) :
    a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c = 506 := by 
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
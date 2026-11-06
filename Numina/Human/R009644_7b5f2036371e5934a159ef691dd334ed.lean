import Mathlib

/- If $(x^2 - k)(x + k) = x^3 + k(x^2 - x - 5)$ and $k\neq 0$, what is the value of $k$? -/
theorem algebra_10710 {x k : ℝ} (h : (x^2 - k) * (x + k) = x^3 + k * (x^2 - x - 5)) (hk : k ≠ 0) :
    k = 5 := by
  apply mul_left_cancel₀ hk
  linarith
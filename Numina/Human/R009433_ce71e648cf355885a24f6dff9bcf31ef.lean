import Mathlib

/- The function $f(x)$ takes positive real numbers to real numbers, such that
\[xf(y) - yf(x) = f \left( \frac{x}{y} \right)\]for all positive real numbers $x$ and $y.$  Find all possible values of $f(100).$  Enter all possible values, separated by commas. -/
theorem algebra_11645 (f : ℝ → ℝ) (h₀ : ∀ x y, 0 < x → 0 < y → x * f y - y * f x = f (x / y)) :
    f 100 = 0 := by
  have h₁ := h₀ 1 100
  have h₂ := h₀ 100 1
  have h₃ := h₀ 1 1
  norm_num at *
  linarith
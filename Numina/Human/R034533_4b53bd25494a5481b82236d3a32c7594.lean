import Mathlib

/- If $23=x^4+\frac{1}{x^4}$, then what is the value of $x^2+\frac{1}{x^2}$? -/
theorem algebra_15734 {x : ℝ} (hx : x ≠ 0) (h : 23 = x ^ 4 + 1 / x ^ 4) :
    x ^ 2 + 1 / x ^ 2 = 5 := by
  field_simp [hx] at h ⊢
  nlinarith
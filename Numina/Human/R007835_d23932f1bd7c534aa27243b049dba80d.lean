import Mathlib

/- If $f(x) = 2$ for all real numbers $x$, what is the value of $f(x + 2)$? -/
theorem algebra_10800 {f : ℝ → ℝ} (h : ∀ x, f x = 2) : f (x + 2) = 2 := by 
  rw [h]
import Mathlib

/- A function $f$ has the property that $f(3x-1)=x^2+x+1$ for all real numbers $x$.  What is $f(5)$? -/
theorem algebra_14318 {f : ℝ → ℝ} (h : ∀ x, f (3 * x - 1) = x ^ 2 + x + 1) : f 5 = 7 := by
  specialize h 2
  norm_num at h
  exact h
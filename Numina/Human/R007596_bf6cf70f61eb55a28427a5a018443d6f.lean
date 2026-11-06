import Mathlib

/- Given the function $f\left(x\right)=ax^{5}+bx^{3}+2$, if $f\left(2\right)=7$, then $f\left(-2\right)=\_\_\_\_\_\_$. -/
theorem algebra_9465 {a b : ℝ} (f : ℝ → ℝ) (hf : ∀ x, f x = a * x ^ 5 + b * x ^ 3 + 2)
    (h : f 2 = 7) : f (-2) = -3 := by
  -- Expand the definition of f
  rw [hf] at *
  -- Remaining a linear problem
  linarith

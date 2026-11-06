import Mathlib

/- Given the function $f(x) = \sin x$, find ${f'}(\frac{π}{2})$. -/
theorem algebra_9072 (f : ℝ → ℝ) (hf : f = Real.sin) : deriv f (Real.pi / 2) = 0 := by
    aesop
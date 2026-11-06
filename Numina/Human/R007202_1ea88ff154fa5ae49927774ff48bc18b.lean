import Mathlib

/- Consider the function $f(x) = 2x^2 - 4x + 9$.  Evaluate $2f(3) + 3f(-3)$. -/
theorem algebra_13850 {f : ℝ → ℝ} (hf : f = fun x => 2 * x ^ 2 - 4 * x + 9) :
    2 * f 3 + 3 * f (-3) = 147 := by
  rw [hf]; ring
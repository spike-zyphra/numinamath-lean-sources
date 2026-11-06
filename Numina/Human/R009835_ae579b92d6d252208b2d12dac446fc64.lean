import Mathlib

/- Given the function $f(x) = x \cdot e^x$, find the value of $f'(0)$.-/
theorem algebra_9200 {f : ℝ → ℝ} (hf : f = fun x => x * Real.exp x) :
    deriv f 0 = 1 := by
  rw [hf, deriv_mul differentiableAt_id' Real.differentiableAt_exp]
  simp

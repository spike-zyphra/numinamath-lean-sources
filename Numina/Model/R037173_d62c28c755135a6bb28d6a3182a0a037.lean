import Mathlib
theorem algebra_610869 (f : ℝ → ℝ → ℝ) (hf : f = fun x y => (x + 2 * y - 1) ^ 6) : f 1 1 = 64:= by
  rw [hf]
  norm_num
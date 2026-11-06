import Mathlib

theorem algebra_13248 {f : ℝ → ℝ} (hf : f = fun x => 5 * x - 4) : f (f (f 2)) = 126 := by
  rw [hf]
  norm_num
  <;> norm_num
  <;> norm_num
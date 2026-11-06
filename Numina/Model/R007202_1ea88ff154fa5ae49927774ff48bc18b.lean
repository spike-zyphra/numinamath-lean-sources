import Mathlib

theorem algebra_13850 {f : ℝ → ℝ} (hf : f = fun x => 2 * x ^ 2 - 4 * x + 9) :
    2 * f 3 + 3 * f (-3) = 147 := by 
  rw [hf]
  norm_num
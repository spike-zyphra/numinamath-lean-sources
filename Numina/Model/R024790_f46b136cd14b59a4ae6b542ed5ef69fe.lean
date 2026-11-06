import Mathlib

theorem algebra_148318 (f : ℝ → ℝ) (hf : f = fun x => -2 * 2^(5 * x - 1) + 4) :
    f 0 = 3 := by 
  rw [hf]
  norm_num
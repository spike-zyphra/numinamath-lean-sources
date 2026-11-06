import Mathlib

theorem algebra_4880 {f : ℝ → ℝ} (hf : f = fun x => 0.5 * x + 1) :
    f (f (f 50)) = 8 := by 
  rw [hf]
  norm_num
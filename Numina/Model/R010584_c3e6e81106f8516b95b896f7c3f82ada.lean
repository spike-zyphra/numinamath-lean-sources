import Mathlib

theorem algebra_9244 (f : ℝ → ℝ) (hf : f = fun x => 4.75 * x + 257) (x : ℝ) (hx : x = 28) : f x = 390 := by 
  rw [hf, hx]
  norm_num
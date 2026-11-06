import Mathlib

theorem calculus_155703 (f : ℝ → ℝ) (hf : f = fun x => x ^ 3) (x0 : ℝ) (y0 : ℝ)
    (h : x0 = -2) (h' : y0 = f x0) :
    deriv f x0 = 12 := by 
  rw [hf, h]
  simp [deriv_pow]
  all_goals norm_num
import Mathlib

theorem algebra_140585 (y c f : ℝ) (hy : y = 3) (hc : c = 5) (hf : f = 1)
    (h : 10 - (1.08 + 3 * 0.52 + 5 * 0.29) = y * 1.08 + c * 0.52 + f * 0.29) :
    y * 1.08 + c * 0.52 + f * 0.29 = 5.91 := by 
  linarith
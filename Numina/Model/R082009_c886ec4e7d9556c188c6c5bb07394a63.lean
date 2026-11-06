import Mathlib

theorem algebra_1364 (w : ℝ) (hw : w > 0) (h : (w + 15) * w ≥ 100) :
    w ≥ 5 := by 
  nlinarith [sq_nonneg (w - 5), sq_nonneg (w + 20), hw]
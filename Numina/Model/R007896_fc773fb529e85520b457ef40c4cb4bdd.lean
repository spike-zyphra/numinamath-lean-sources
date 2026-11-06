import Mathlib

theorem algebra_14899 {b c : ℝ} (h : (-1)^2 + b * (-1) + c = -11) (h' : 3^2 + b * 3 + c = 17) :
    c = -7 := by 
  linarith
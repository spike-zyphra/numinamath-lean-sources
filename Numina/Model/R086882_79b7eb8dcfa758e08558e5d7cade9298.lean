import Mathlib

theorem algebra_219492 (a b c : ℝ) (h : (3 : ℝ)^4 + a * (3^2) + b * 3 + c = 0)
    (h' : (-2)^4 + a * (-2)^2 + b * (-2) + c = 0) (h'' : 5^4 + a * 5^2 + b * 5 + c = 0) :
    a + b + c = 167 := by
  norm_num at h h' h''
  linarith
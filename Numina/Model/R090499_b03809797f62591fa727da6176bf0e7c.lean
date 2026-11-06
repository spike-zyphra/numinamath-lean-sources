import Mathlib

theorem algebra_304981 {a b c : ℝ} (h : a * (-3)^5 + b * (-3)^3 + c * (-3) - 5 = 7) :
    a * (3)^5 + b * (3)^3 + c * (3) - 5 = -17 := by
  have eq1 : a * (-3) ^ 5 + b * (-3) ^ 3 + c * (-3) = 12 := by
    linarith
  have eq3 : a * (-3) ^ 5 + b * (-3) ^ 3 + c * (-3) = - (a * (3) ^ 5 + b * (3) ^ 3 + c * (3)) := by
    ring
  have eq2 : a * (3) ^ 5 + b * (3) ^ 3 + c * (3) = -12 := by
    linarith [eq3, eq1]
  linarith [eq2]
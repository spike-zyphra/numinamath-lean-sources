import Mathlib

theorem algebra_142665 (a b c : ℝ) (h₁ : 4*a*1^3+3*b*1^2-2*c*1=8) (h₂ : 3*a*1^3+2*b*1^2-c*1=-6) :
    10*a*(-1)^3-7*b*(-1)^2-4*c*(-1)+2016=2020 := by
  have eq1 : 10 * a * (-1)^3 - 7 * b * (-1)^2 - 4 * c * (-1) + 2016
    = -10 * a - 7 * b + 4 * c + 2016 := by 
    ring
  rw [eq1]
  linarith
import Mathlib

theorem algebra_5168 {a b c d : ℝ} :
    a*b*c*(a+b+c) + b*c*d*(b+c+d) + c*d*a*(c+d+a) +
    d*a*b*(d+a+b) + (a*b+c*d)^2 =
    (a+d)*(a+c)*(b+d)*(b+c) := by
  ring
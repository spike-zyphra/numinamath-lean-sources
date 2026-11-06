import Mathlib

open Real
open scoped BigOperators
/-If a, b and c are sides of triangle which perimeter equals 1,
prove that: a^2+b^2+c^2+4abc<1/2-/
theorem inequalities_33213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 1) :
  a^2 + b^2 + c^2 + 4*a*b*c < 1/2 := by
    have h14 : (1 / 2 - a) * (1 / 2 - b) * (1 / 2 - c) > 0 := by
      apply mul_pos
      apply mul_pos
      all_goals linarith
    nlinarith [h14]
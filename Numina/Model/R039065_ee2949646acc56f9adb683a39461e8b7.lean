import Mathlib

open Real
open scoped BigOperators
theorem inequalities_33213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (h''' : a + b + c = 1) :
  a^2 + b^2 + c^2 + 4*a*b*c < 1/2 := by 
  have h1 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    all_goals linarith
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
            mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
            mul_pos (sub_pos.mpr h') (sub_pos.mpr h'')
          ]
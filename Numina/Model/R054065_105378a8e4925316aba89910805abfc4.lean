import Mathlib

open Real
open scoped BigOperators

theorem inequalities_69219 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^3 + b^3 + 3*a*b*c > c^3 := by 
  have h1 : a + b - c > 0 := by linarith 
  have h2 : a^2 + b^2 + c^2 - a*b + a*c + b*c > 0 := by
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have h3 : (a + b - c) * (a^2 + b^2 + c^2 - a*b + a*c + b*c) > 0 := by
    apply mul_pos
    all_goals linarith 
  nlinarith [h3]
import Mathlib

open Real
open scoped BigOperators

theorem inequalities_36136 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
  have pos1 : b + c > 0 := by nlinarith
  have pos2 : c + a > 0 := by nlinarith
  have pos3 : a + b > 0 := by nlinarith
  
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 2 < 0 := by
    have z : (a / (b + c) + b / (c + a) + c / (a + b) - 2) = ( (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) ) := by
      field_simp
      <;> ring
    rw [z]
    have pos4 : (b + c) * (c + a) * (a + b) > 0 := by
      positivity
    have y : a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b) < 0 := by
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b), mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), mul_pos (sub_pos.mpr h) (sub_pos.mpr h'') ]
    apply div_neg_of_neg_of_pos
    linarith
    positivity
  
  linarith
  all_goals linarith
  all_goals linarith
  all_goals positivity
  all_goals positivity
  all_goals linarith
  all_goals positivity
  all_goals linarith
  all_goals nlinarith
  all_goals positivity
  all_goals linarith
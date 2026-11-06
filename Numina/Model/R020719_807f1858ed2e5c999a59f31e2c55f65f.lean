import Mathlib

open Real
open scoped BigOperators

theorem inequalities_154569 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
  have pos1 : 0 < b + c := by linarith
  have pos2 : 0 < c + a := by linarith
  have pos3 : 0 < a + b := by linarith
  have h1 : a / (b + c) + b / (c + a) + c / (a + b) - 2 < 0 := by
    have pos1 : 0 < (b + c) * (c + a) * (a + b) := by positivity
    have h2 : a / (b + c) + b / (c + a) + c / (a + b) - 2 =
        (a * (c + a) * (a + b) + b * (b + c) * (a + b) + c * (b + c) * (c + a) - 2 * (b + c) * (c + a) * (a + b)) / ((b + c) * (c + a) * (a + b)) := by
      field_simp
      <;> ring
    rw [h2] at *
    apply div_neg_of_neg_of_pos
    · -- Show the numerator is negative
      nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
        mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
        mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
        sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
        mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith), 
        mul_pos (show 0 < a + b - c by linarith) (show 0 < c + a - b by linarith), 
        mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith)
      ]
    · -- Show the denominator is positive
      positivity
  linarith
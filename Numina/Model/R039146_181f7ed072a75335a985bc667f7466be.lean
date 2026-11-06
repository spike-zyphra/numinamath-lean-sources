import Mathlib

open Real
open scoped BigOperators

theorem inequalities_170097 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (h''' : a + b + c = 1) :
  a^2 + b^2 + c^2 + 4 * a * b * c < 1 / 2 := by 
  have h1 : c = 1 - a - b := by linarith
  have h2 : a + b > 1 / 2 := by nlinarith
  have h3 : a < 1 / 2 := by nlinarith
  have h4 : b < 1 / 2 := by nlinarith
  have h5 : a * b > 0 := mul_pos ha hb
  rw [h1]
  nlinarith [mul_pos ha hb, mul_pos ha (show 0 < 1 - a - b by nlinarith), mul_pos hb (show 0 < 1 - a - b by nlinarith), mul_pos (show 0 < 1 - a - b by nlinarith) (show 0 < 1 - a - b by nlinarith), mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), mul_pos (sub_pos.mpr h'') (sub_pos.mpr h)]
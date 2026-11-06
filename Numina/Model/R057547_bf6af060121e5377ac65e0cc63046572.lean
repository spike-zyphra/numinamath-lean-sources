import Mathlib

open Real

theorem inequalities_169682 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (h''' : a + b + c = 1) :
    a^2 + b^2 + c^2 + 4 * a * b * c < 1 / 2 := by
  nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (sub_pos.mpr (show a + b > c by linarith)) (sub_pos.mpr (show b + c > a by linarith)),
          mul_pos (sub_pos.mpr (show b + c > a by linarith)) (sub_pos.mpr (show c + a > b by linarith)),
          mul_pos (sub_pos.mpr (show a + b > c by linarith)) (sub_pos.mpr (show c + a > b by linarith)),
          mul_pos (sub_pos.mpr (show 0 < c by linarith)) (sub_pos.mpr (show 0 < a by linarith)),
          mul_pos (sub_pos.mpr (show 0 < b by linarith)) (sub_pos.mpr (show 0 < c by linarith)),
          mul_pos (sub_pos.mpr (show 0 < a by linarith)) (sub_pos.mpr (show 0 < b by linarith)),
          mul_pos (sub_pos.mpr (show 0 < b by linarith)) (sub_pos.mpr (show 0 < c by linarith)),
          mul_pos (sub_pos.mpr (show 0 < a by linarith)) (sub_pos.mpr (show 0 < c by linarith)),
          mul_pos (sub_pos.mpr (show 0 < c by linarith)) (sub_pos.mpr (show 0 < b by linarith)),
          mul_pos (sub_pos.mpr (show a + b > c by linarith)) (sub_pos.mpr (show b + c > a by linarith)),
          mul_pos (sub_pos.mpr (show b + c > a by linarith)) (sub_pos.mpr (show c + a > b by linarith)),
          mul_pos (sub_pos.mpr (show a + b > c by linarith)) (sub_pos.mpr (show c + a > b by linarith)),
          h''', mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
import Mathlib

theorem inequalities_277105 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c) :
    (a + 1) * (b + 1) * (a + c) * (b + c) > 16 * a * b * c := by
  have ha1 : a - 1 > 0 := by linarith
  have hb1 : b - 1 > 0 := by linarith
  have hc1 : c - 1 > 0 := by linarith
  have ha2 : (a - 1) * (b - 1) > 0 := by nlinarith
  have ha3 : (a - 1) * (c - 1) > 0 := by nlinarith
  have ha4 : (b - 1) * (c - 1) > 0 := by nlinarith
  have h6 : (a + 1) * (b + 1) * (a + c) * (b + c) - 16 * a * b * c > 0 := by
    nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc),
          mul_pos (show 0 < a * b by nlinarith) (show 0 < c by nlinarith),
          sq_nonneg (a * b - a * c), 
          sq_nonneg (b * c - a * b), 
          sq_nonneg (a - b), 
          sq_nonneg (a - c), 
          sq_nonneg (b - c),
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb),
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc), 
          mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), 
          mul_pos (show 0 < a - 1 by linarith) (show 0 < b - 1 by linarith), 
          mul_pos (show 0 < a - 1 by linarith) (show 0 < c - 1 by linarith), 
          mul_pos (show 0 < b - 1 by linarith) (show 0 < c - 1 by linarith), 
          sq_pos_of_pos (show a - 1 > 0 by linarith), 
          sq_pos_of_pos (show b - 1 > 0 by linarith), 
          sq_pos_of_pos (show c - 1 > 0 by linarith)
          ]
  linarith
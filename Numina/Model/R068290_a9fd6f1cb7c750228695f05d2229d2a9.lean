import Mathlib

theorem inequalities_276906 (a b c : ℝ) (ha : a < b) (hb : b < c) :
    a^2 * b + b^2 * c + c^2 * a < a^2 * c + b^2 * a + c^2 * b := by 
  have h1 : a < b := ha
  have h2 : b < c := hb
  have h3 : a < c := by linarith
  
  nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr (show a < c by linarith)), 
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr (show a < c by linarith)), 
          mul_pos (sub_pos.mpr h1) (show 0 < c - b from by linarith), 
          mul_pos (sub_pos.mpr h2) (show 0 < b - a from by linarith), 
          mul_pos (show 0 < b - a from by linarith) (show 0 < c - b from by linarith), 
          sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
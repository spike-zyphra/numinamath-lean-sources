import Mathlib

theorem inequalities_604693 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h1 : a < 1) (h2 : b < 1) (h3 : c < 1) (h4 : d < 1) :
    1 + a * b + b * c + c * d + d * a + a * c + b * d > a + b + c + d := by 
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc, 
            mul_pos hb hd, mul_pos hc hd, 
            mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
            mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
            mul_pos (sub_pos.mpr h1) (sub_pos.mpr h4), 
            mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), 
            mul_pos (sub_pos.mpr h2) (sub_pos.mpr h4), 
            mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4)]
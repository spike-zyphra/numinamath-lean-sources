import Mathlib

theorem inequalities_304722 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a < 1) (h1 : b < 1) (h2 : c < 1) (h3 : d < 1) :
    2 > a * (1 - b) + b * (1 - c) + c * (1 - d) + d * (1 - a) := by 
  nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos ha hd, mul_pos hb hc,
          mul_pos hb hd, mul_pos hc hd,
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h1), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h2), 
          mul_pos (sub_pos.mpr h) (sub_pos.mpr h3), 
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), 
          mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), 
          mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), 
          mul_pos ha (sub_pos.mpr h), 
          mul_pos hb (sub_pos.mpr h1), 
          mul_pos hc (sub_pos.mpr h2), 
          mul_pos hd (sub_pos.mpr h3)
        ]
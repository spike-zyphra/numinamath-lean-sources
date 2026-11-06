import Mathlib

theorem inequalities_264425 (a b c : ℝ) (ha : 1 / 2 < a) (hb : 1 / 2 < b) (hc : 1 / 2 < c)
    (h : a * b + b * c + c * a = 5 / 4) :
    a + b + c > a ^ 2 + b ^ 2 + c ^ 2 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), mul_pos (sub_pos.mpr hb) (sub_pos.mpr hc), mul_pos (sub_pos.mpr ha) (sub_pos.mpr hc)]
import Mathlib

theorem inequalities_207026 (a b : ℝ) (ha : a > 1 / 2) (hb : b > 1 / 2) :
    a + 2 * b - 5 * a * b < 1 / 4 := by
  nlinarith [mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb), 
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          sq_nonneg (a - 1 / 2), sq_nonneg (b - 1 / 2), 
          mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)
        ]
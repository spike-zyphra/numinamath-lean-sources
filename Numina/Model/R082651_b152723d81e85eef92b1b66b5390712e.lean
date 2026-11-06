import Mathlib

theorem inequalities_208527 (x y : ℝ) (hx : 1 < x) (hy : 1 < y) :
    8 ≤ x^2 / (y - 1) + y^2 / (x - 1) := by
  have h1 : 0 < y - 1 := by linarith
  have h2 : 0 < x - 1 := by linarith
  have h3 : x^2 / (y - 1) + y^2 / (x - 1) - (8 : ℝ) ≥ 0 := by
    have h4 : x^2 / (y - 1) + y^2 / (x - 1) - (8 : ℝ)
        = (x^2 * (x - 1) + y^2 * (y - 1) - 8 * (y - 1) * (x - 1)) / ((y - 1) * (x - 1)) := by
      field_simp
      ring
    rw [h4]
    have h5 : x^2 * (x - 1) + y^2 * (y - 1) - 8 * (y - 1) * (x - 1) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - 2), sq_nonneg (x - 2), sq_nonneg (y - 2),
        mul_pos h1 h2, mul_pos (sub_pos.mpr hx) (sub_pos.mpr hy)]
    have h6 : (y - 1) * (x - 1) > 0 := mul_pos h1 h2
    apply div_nonneg
    linarith
    linarith
  linarith
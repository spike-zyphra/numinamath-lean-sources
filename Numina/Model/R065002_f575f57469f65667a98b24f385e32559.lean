import Mathlib

theorem inequalities_213843 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x^2 + 8 / (x * y) + y^2 ≥ 8 := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : x^2 + 8 / (x * y) + y^2 - 8 ≥ 0 := by
    have h3 : x^2 + 8 / (x * y) + y^2 - 8 = (x^2 * (x * y) + 8 + y^2 * (x * y) - 8 * (x * y)) / (x * y) := by
      field_simp
      ring
    rw [h3]
    have h4 : x^2 * (x * y) + 8 + y^2 * (x * y) - 8 * (x * y) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x * y - 2), sq_nonneg (x * y), sq_nonneg (x - 2), sq_nonneg (y - 2),
        mul_pos hx hy, mul_pos hx (show 0 < y by linarith), mul_pos (show 0 < x by linarith) hy]
    have h5 : (x * y) > 0 := by
      positivity
    have h6 : (x^2 * (x * y) + 8 + y^2 * (x * y) - 8 * (x * y)) / (x * y) ≥ 0 := by
      apply div_nonneg
      linarith
      positivity
    linarith
  linarith
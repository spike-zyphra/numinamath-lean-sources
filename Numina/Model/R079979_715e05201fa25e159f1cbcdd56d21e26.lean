import Mathlib

theorem inequalities_323962 (x y : ℝ) (hx : abs x < 1) (hy : abs y < 1) :
    1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) ≥ 2 / (1 - x * y) := by
  have h1 : -1 < x := by
    linarith [abs_lt.mp hx]
  have h2 : x < 1 := by
    linarith [abs_lt.mp hx]
  have h3 : -1 < y := by
    linarith [abs_lt.mp hy]
  have h4 : y < 1 := by
    linarith [abs_lt.mp hy]
  have h5 : 0 < 1 - x ^ 2 := by
    nlinarith
  have h6 : 0 < 1 - y ^ 2 := by
    nlinarith
  have h8 : 0 < 1 - x * y := by
    nlinarith [mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h4), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h4)]
  have h9 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) ≥ 0 := by
    have h10 : 0 < (1 - x^2) * (1 - y^2) * (1 - x * y) := by positivity
    have h11 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) =
        ( (2 - x^2 - y^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2) ) / ( (1 - x^2) * (1 - y^2) * (1 - x * y) ) := by
      field_simp
      ring
    rw [h11]
    have h12 : (2 - x^2 - y^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x * y - 1), sq_nonneg (x * y), sq_nonneg (x * (x - y)), sq_nonneg (y * (y - x)), mul_nonneg (show 0 ≤ 1 - x^2 by nlinarith) (show 0 ≤ 1 - y^2 by nlinarith), sq_nonneg (x * y - x - y)]
    apply div_nonneg
    linarith
    positivity
  linarith
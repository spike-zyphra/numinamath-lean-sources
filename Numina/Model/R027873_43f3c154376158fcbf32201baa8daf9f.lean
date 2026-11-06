import Mathlib

theorem inequalities_326010 (x y : ℝ) (hx : |x| < 1) (hy : |y| < 1) :
    1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) ≥ 2 / (1 - x * y) := by
  have h1 : -1 < x := by linarith [abs_lt.mp hx]
  have h2 : x < 1 := by linarith [abs_lt.mp hx]
  have h3 : -1 < y := by linarith [abs_lt.mp hy]
  have h4 : y < 1 := by linarith [abs_lt.mp hy]

  have hx2_pos : 0 < 1 - x ^ 2 := by nlinarith
  have hy2_pos : 0 < 1 - y ^ 2 := by nlinarith

  have hxy_pos : 0 < 1 - x * y := by
    nlinarith [abs_lt.mp hx, abs_lt.mp hy, mul_pos (show (0 : ℝ) < 1 - x by nlinarith) (show (0 : ℝ) < 1 - y by nlinarith)]

  have h6 : (1 - x * y) * (1 - y ^ 2) + (1 - x * y) * (1 - x ^ 2) - 2 * (1 - x ^ 2) * (1 - y ^ 2) ≥ 0 := by
    nlinarith [sq_nonneg (x + y), sq_nonneg (x - y), sq_nonneg (x * y - x), sq_nonneg (x * y - y), sq_nonneg (x - y), sq_nonneg (x + y), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h2), mul_pos (sub_pos.mpr h3) (sub_pos.mpr h4), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h1) (sub_pos.mpr h4), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h3), mul_pos (sub_pos.mpr h2) (sub_pos.mpr h4), sq_nonneg (x * y), sq_nonneg (x - y)]

  have h7 : 1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y) ≥ 0 := by
    have pos1 : 0 < (1 - x ^ 2) := hx2_pos
    have pos2 : 0 < (1 - y ^ 2) := hy2_pos
    have pos3 : 0 < (1 - x * y) := hxy_pos
    have h8 : (1 - x ^ 2) * (1 - y ^ 2) * (1 - x * y) > 0 := by positivity
    have h9 : (1 / (1 - x ^ 2) + 1 / (1 - y ^ 2) - 2 / (1 - x * y)) =
        ((1 - x * y) * (1 - y ^ 2) + (1 - x * y) * (1 - x ^ 2) - 2 * (1 - x ^ 2) * (1 - y ^ 2)) / ((1 - x ^ 2) * (1 - y ^ 2) * (1 - x * y)) := by
      field_simp [(show 1 - x ^ 2 ≠ 0 by nlinarith), (show 1 - y ^ 2 ≠ 0 by nlinarith), (show 1 - x * y ≠ 0 by nlinarith)]
      ring
    rw [h9]
    apply div_nonneg
    linarith
    all_goals positivity

  linarith [h7]
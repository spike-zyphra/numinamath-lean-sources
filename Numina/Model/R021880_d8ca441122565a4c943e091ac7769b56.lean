import Mathlib

theorem inequalities_33311 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxp : x < 1) (hyq : y < 1) :
    1 / 2 ≤ x ^ 2 / (x + y) + y ^ 2 / (1 - x) + (1 - x - y) ^ 2 / (1 - y) := by
  have hx1 : 0 < x := hx
  have hy1 : 0 < y := hy
  have hx2 : x < 1 := hxp
  have hy2 : y < 1 := hyq
  have h1 : 0 < x + y := by linarith
  have h2 : 0 < 1 - x := by linarith
  have h3 : 0 < 1 - y := by linarith
  have h4 : x ^ 2 / (x + y) + y ^ 2 / (1 - x) + (1 - x - y) ^ 2 / (1 - y) - 1 / 2 ≥ 0 := by
    have pos1 : 0 < (x + y) * (1 - x) * (1 - y) := by positivity
    have h5 : (x ^ 2 / (x + y) + y ^ 2 / (1 - x) + (1 - x - y) ^ 2 / (1 - y) - 1 / 2) = (x^2 * (1 - x) * (1 - y) + y^2 * (x + y) * (1 - y) + (1 - x - y)^2 * (x + y) * (1 - x) - 1 / 2 * (x + y) * (1 - x) * (1 - y)) / ((x + y) * (1 - x) * (1 - y)) := by
      field_simp
      ring
    rw [h5]
    apply div_nonneg
    -- Show the numerator is non-negative
    have h8 : x^2 * (1 - x) * (1 - y) + y^2 * (x + y) * (1 - y) + (1 - x - y)^2 * (x + y) * (1 - x) - 1 / 2 * (x + y) * (1 - x) * (1 - y) ≥ 0 := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - (1 - x - y)), sq_nonneg (y - (1 - x - y)), sq_nonneg (x + y - 1/2), sq_nonneg ((1 - x) - 1/2), sq_nonneg ((1 - y) - 1/2), mul_pos hx hy, mul_pos hx (show 0 < 1 - x by linarith), mul_pos hy (show 0 < 1 - x by linarith), mul_pos hx (show 0 < 1 - y by linarith), mul_pos hy (show 0 < 1 - y by linarith), mul_pos (show 0 < 1 - x by linarith) (show 0 < 1 - y by linarith)]
    linarith
    all_goals positivity
  linarith
import Mathlib

theorem inequalities_599605 (x y : ℝ) (hx : -1 < x) (hy : -1 < y)
    (hxy : x < 1 ∧ y < 1) :
    2 / (1 - x * y) ≤ 1 / (1 - y ^ 2) + 1 / (1 - x ^ 2) := by
  have hx1 : -1 < x := hx
  have hy1 : -1 < y := hy
  have hx2 : x < 1 := hxy.1
  have hy2 : y < 1 := hxy.2
  have h2 : 0 < 1 - x * y := by
    nlinarith [mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hy2), 
              sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1)]
  have h5 : 0 < (1 - y ^ 2 : ℝ) := by
    have h6 : -1 < y := hy
    have h7 : y < 1 := hy2
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 - y by linarith), sq_nonneg (y + 1)]
  have h6 : 0 < (1 - x ^ 2 : ℝ) := by
    have h7 : -1 < x := hx
    have h8 : x < 1 := hx2
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 1 - x by linarith), sq_nonneg (x + 1)]
  have h4 : 0 ≤ 1 / (1 - y ^ 2) + 1 / (1 - x ^ 2) - 2 / (1 - x * y) := by
    have h5 : 0 < (1 - y ^ 2 : ℝ) := h5
    have h6 : 0 < (1 - x ^ 2 : ℝ) := h6
    have h2 : 0 < (1 - x * y : ℝ) := h2
    have h10 : 1 / (1 - y ^ 2) + 1 / (1 - x ^ 2) - 2 / (1 - x * y) =
        ((1 - x^2) * (1 - x * y) + (1 - y^2) * (1 - x * y) - 2 * (1 - x^2) * (1 - y^2)) / ((1 - y ^ 2) * (1 - x ^ 2) * (1 - x * y)) := by
      field_simp
      <;> ring
    rw [h10]
    apply div_nonneg
    · -- proving the numerator is non-negative
      nlinarith [sq_nonneg (x - y), sq_nonneg (x + y), sq_nonneg (x - y), 
          sq_nonneg (x * y - x), sq_nonneg (x * y - y), 
          sq_nonneg (x + 1), sq_nonneg (y + 1), 
          sq_nonneg (x - y), 
          mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hy2), 
          mul_pos (sub_pos.mpr hx2) (sub_pos.mpr hx2), 
          mul_pos (sub_pos.mpr hy1) (sub_pos.mpr hy1)
      ]
    · -- proving the denominator is non-negative
      positivity
  linarith [h4]
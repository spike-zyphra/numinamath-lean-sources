import Mathlib

theorem inequalities_87018 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
    x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) ≤ 1 / (x * y) := by
  have h1 : 0 < x * y := mul_pos hx hy
  have h2 : x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) - 1 / (x * y) ≤ 0 := by
    have h3 : 0 < (x ^ 4 + y ^ 2) := by
      have hx4_pos : 0 < x ^ 4 := by positivity
      have hy2_pos : 0 < y ^ 2 := by positivity
      linarith [hx4_pos, hy2_pos]
    have h4 : 0 < x ^ 2 + y ^ 4 := by
      have hx2_pos : 0 < x ^ 2 := by positivity
      have hy4_pos : 0 < y ^ 4 := by positivity
      linarith [hx2_pos, hy4_pos]
    have h6 : x / (x ^ 4 + y ^ 2) + y / (x ^ 2 + y ^ 4) - 1 / (x * y) = (x * (x * y) * (x ^ 2 + y ^ 4) + y * (x * y) * (x ^ 4 + y ^ 2) - (x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4)) / ((x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4) * (x * y)) := by 
      field_simp
      ring 
    rw [h6]
    have h7 : (x * (x * y) * (x ^ 2 + y ^ 4) + y * (x * y) * (x ^ 4 + y ^ 2) - (x ^ 4 + y ^ 2) * (x ^ 2 + y ^ 4)) ≤ 0 := by
      nlinarith [sq_nonneg (x ^ 2 - y), sq_nonneg (x - y ^ 2), sq_nonneg (x * y - x * y ^ 2), sq_nonneg (x * y ^ 2 - x ^ 2 * y ^ 2), sq_nonneg (x^4 - y^2), sq_nonneg (x^2 - y^4), sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * (x^2 - y)), sq_nonneg (y * (x - y^2)), mul_pos hx hy, mul_pos (show 0 < x^2 from by positivity) (show 0 < y^2 from by positivity),
                  mul_pos (show 0 < x^4 from by positivity) (show 0 < y^4 from by positivity)]
    apply div_nonpos_of_nonpos_of_nonneg 
    · linarith
    · positivity
  linarith
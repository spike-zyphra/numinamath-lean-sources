import Mathlib

theorem inequalities_74341 (x y z : ℝ) (h : x * y * z = -1) :
    x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x + y + z) ≥ x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z +
    z ^ 2 / x + z ^ 2 / y := by
  have h1 : x ≠ 0 := by
    by_contra hx
    have h0 : x * y * z = 0 := by
      rw [hx]
      norm_num
    linarith
  have h2 : y ≠ 0 := by
    by_contra hy
    have h0 : x * y * z = 0 := by
      rw [hy]
      norm_num
    linarith
  have h3 : z ≠ 0 := by
    by_contra hz
    have h0 : x * y * z = 0 := by
      rw [hz]
      norm_num
    linarith
  have h4 : x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y = 
    (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * x + z^3 * y) / (x * y * z) := by 
    field_simp [h1, h2, h3]
    ring
  rw [h4]
  have h5 : (x ^ 3 * z + x ^ 3 * y + y ^ 3 * z + y ^ 3 * x + z ^ 3 * x + z ^ 3 * y) / (x * y * z) = - (x^3 * z + x ^ 3 * y + y ^ 3 * z + y ^ 3 * x + z ^ 3 * x + z ^ 3 * y) := by
    have h6 : x * y * z = -1 := h
    have h66 : x * y * z ≠ 0 := by 
      rw [h6]
      norm_num
    field_simp [h66, h6]
    all_goals nlinarith
  rw [h5]
  have h6 : x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x + y + z) ≥ - (x^3 * z + x ^ 3 * y + y ^ 3 * z + y ^ 3 * x + z ^ 3 * x + z ^ 3 * y) := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (y^2 - z^2), sq_nonneg (z^2 - x^2),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z),
          sq_nonneg (x * y + y * z + z * x),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (y - z)),
          sq_nonneg (y * (x - y)), sq_nonneg (y * (x - z)), sq_nonneg (y * (y - z)),
          sq_nonneg (z * (x - y)), sq_nonneg (z * (x - z)), sq_nonneg (z * (y - z)),
          h]
  linarith
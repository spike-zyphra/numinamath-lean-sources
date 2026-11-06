import Mathlib

theorem inequalities_67635 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y + y * z + z * x = 1) :
    2 * (x ^ 2 + y ^ 2 + z ^ 2) +
    (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) ≥ 5 := by
  have h1 : x * y + y * z + z * x = 1 := h
  have hx2 : 0 < x ^ 2 := by nlinarith
  have hy2 : 0 < y ^ 2 := by nlinarith
  have hz2 : 0 < z ^ 2 := by nlinarith
  have hx2_1 : x ^ 2 + 1 > 0 := by nlinarith
  have hy2_1 : y ^ 2 + 1 > 0 := by nlinarith
  have hz2_1 : z ^ 2 + 1 > 0 := by nlinarith
  -- Set up clear denominators
  have h2 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5 ≥ 0 := by
    have h3 : (2 * (x ^ 2 + y ^ 2 + z ^ 2) + (4 / 3) * (1 / (x ^ 2 + 1) + 1 / (y ^ 2 + 1) + 1 / (z ^ 2 + 1)) - 5) = 
        (2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) +
          (4 / 3) * ((y ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (y ^ 2 + 1)) - 5 * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1)) / ((x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1)) := by
      field_simp
      ring
    rw [ h3 ]
    have h6 : (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) > 0 := by positivity
    have h7 : 2 * (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) +
                  (4 / 3) * ( (y ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (z ^ 2 + 1) + (x ^ 2 + 1) * (y ^ 2 + 1) ) - 5 * (x ^ 2 + 1) * (y ^ 2 + 1) * (z ^ 2 + 1) ≥ 0 := by
      have eq1 : x ^ 2 + 1 = x ^ 2 + 1 := rfl
      have eq2 : y ^ 2 + 1 = y ^ 2 + 1 := rfl
      have eq3 : z ^ 2 + 1 = z ^ 2 + 1 := rfl
      nlinarith [ sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z),
                  sq_nonneg (x * y - y * z), sq_nonneg (x * y - z * x), sq_nonneg (y * z - z * x),
                  sq_nonneg (x * y * z), h1, mul_pos hx hy, mul_pos hy hz, mul_pos hz hx ]

    apply div_nonneg
    linarith
    all_goals positivity
  linarith
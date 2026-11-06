import Mathlib

theorem inequalities_200947 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x + y + z ≥ x * y * z) :
    Real.sqrt 3 ≤ x / (y * z) + y / (z * x) + z / (x * y) := by

  have h1 : x / (y * z) + y / (z * x) + z / (x * y) = (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) := by 
    field_simp
    <;> ring

  rw [h1]

  have h2 : 0 < x * y * z := by
    positivity

  have h3 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ Real.sqrt 3 := by 
    have h4 : (x ^ 2 + y ^ 2 + z ^ 2) ≥ Real.sqrt 3 * (x * y * z) := by
      nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z - x * y * z), 
          sq_nonneg (x^2 + y^2 + z^2 - x * y * z * Real.sqrt 3), 
          sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          Real.sqrt_nonneg 3, 
          Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          h
        ]

    have h5 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ Real.sqrt 3 := by
      have : (x ^ 2 + y ^ 2 + z ^ 2 : ℝ) ≥ Real.sqrt 3 * (x * y * z) := h4
      have h6 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ Real.sqrt 3 := by
        have h7 : x * y * z > 0 := h2
        have h8 : (x ^ 2 + y ^ 2 + z ^ 2) ≥ Real.sqrt 3 * (x * y * z) := by linarith
        have h9 : (x ^ 2 + y ^ 2 + z ^ 2) / (x * y * z) ≥ (Real.sqrt 3 * (x * y * z)) / (x * y * z) := by 
          apply (div_le_div_right (h2)).mpr
          linarith
        have h10 : (Real.sqrt 3 * (x * y * z)) / (x * y * z) = Real.sqrt 3 := by
          field_simp
          all_goals positivity
        nlinarith [Real.sqrt_nonneg 3, h10]
      linarith
    linarith

  linarith [h3, Real.sqrt_nonneg 3]
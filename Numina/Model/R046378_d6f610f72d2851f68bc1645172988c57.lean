import Mathlib

theorem inequalities_598095 (x y z : ℝ) (h : x * y * z = -1) :
    x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x + y + z) ≥
    x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y := by 
  have h1 : x ≠ 0 := by 
    by_contra hx
    have h2 : x * y * z = 0 := by 
      rw [hx]
      norm_num 
    linarith 
  have h2 : y ≠ 0 := by
    by_contra hy
    have h3 : x * y * z = 0 := by 
      rw [hy]
      norm_num 
    linarith
  have h3 : z ≠ 0 := by
    by_contra hz
    have h4 : x * y * z = 0 := by 
      rw [hz]
      norm_num 
    linarith
  have h4 : x * y * z = -1 := h 
  have h5 : x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y = (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * y + z^3 * x) / (x * y * z) := by 
    field_simp
    ring 
  have h6 : x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y = (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * y + z^3 * x) / (x * y * z) := h5 
  have h5 : x ^ 4 + y ^ 4 + z ^ 4 + 3 * (x + y + z) ≥ x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y := by 
    have eq1 : (x ^ 2 / y + x ^ 2 / z + y ^ 2 / x + y ^ 2 / z + z ^ 2 / x + z ^ 2 / y) = (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * y + z^3 * x) / (x * y * z) := h5 
    rw [eq1]
    have h8 : x * y * z = -1 := h4 
    have h9 : (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * y + z^3 * x) / (x * y * z) = - (x^3 * z + x^3 * y + y^3 * z + y^3 * x + z^3 * y + z^3 * x) := by
      have h10 : x * y * z = -1 := h8
      have hxy : x * y * z ≠ 0 := by
        apply mul_ne_zero 
        apply mul_ne_zero 
        exact h1 
        exact h2 
        exact h3 
      field_simp [hxy, h10] 
      all_goals linarith
    rw [h9]
    nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (y ^ 2 - z ^ 2), sq_nonneg (z ^ 2 - x ^ 2),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x + y + z),
          sq_nonneg (x * y + y * z + z * x),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          sq_nonneg (x * y * z + 1), sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          h, mul_ne_zero (show (x) ≠ 0 by assumption) (show (y) ≠ 0 by assumption), 
          mul_ne_zero (show (x) ≠ 0 by assumption) (show (z) ≠ 0 by assumption), 
          mul_ne_zero (show (y) ≠ 0 by assumption) (show (z) ≠ 0 by assumption)
        ]
  exact h5
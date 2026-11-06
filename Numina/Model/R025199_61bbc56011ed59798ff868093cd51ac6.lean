import Mathlib

theorem inequalities_603506 (x y z : ℝ) (h : x * y * z = 8) :
    2 / (2 + x ^ 2) + 2 / (2 + y ^ 2) + 2 / (2 + z ^ 2) ≥ 1 := by 
  have h1 : 0 < (2 + x ^ 2) * (2 + y ^ 2) * (2 + z ^ 2) := by positivity
  have h2 : 2 / (2 + x ^ 2) + 2 / (2 + y ^ 2) + 2 / (2 + z ^ 2) - 1 ≥ 0 := by
    have pos1 : 0 < (2 + x^2) * (2 + y^2) * (2 + z^2) := h1
    have eq1 : 2 / (2 + x ^ 2) + 2 / (2 + y ^ 2) + 2 / (2 + z ^ 2) - 1 =
        (2 * (2 + y^2) * (2 + z^2) + 2 * (2 + x^2) * (2 + z^2) + 2 * (2 + x^2) * (2 + y^2) - (2 + x^2) * (2 + y^2) * (2 + z^2)) / ((2 + x^2) * (2 + y^2) * (2 + z^2)) := by
      field_simp
      <;> ring
    rw [eq1] at *
    apply div_nonneg
    -- Prove the numerator is non-negative
    have h3 : 2 * (2 + y ^ 2) * (2 + z ^ 2) + 2 * (2 + x ^ 2) * (2 + z ^ 2) + 2 * (2 + x ^ 2) * (2 + y ^ 2) - (2 + x^2) * (2 + y ^ 2) * (2 + z ^ 2) ≥ 0 := by
      have h4 : x^2 * y^2 * z^2 = 64 := by 
        have h5 : x * y * z = 8 := h 
        have h6 : x^2 * y^2 * z^2 = (x * y * z) ^ 2 := by ring 
        rw [h6, h5]
        all_goals norm_num
      nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (y^2 - 4), sq_nonneg (z^2 - 4),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
            h4, sq_nonneg (x * y * z - 8), 
          sq_nonneg (x + y + z),
          sq_nonneg (x * y + y * z + z * x - 12)]
    linarith
    -- Prove the denominator is positive
    positivity
  linarith
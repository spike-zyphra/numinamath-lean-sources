import Mathlib

open Real

theorem inequalities_314500 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2 ≤ x / sqrt (y ^ 2 + z ^ 2) + y / sqrt (x ^ 2 + z ^ 2) +
        z / sqrt (x ^ 2 + y ^ 2) := by
  have h1 : x / sqrt (y^2 + z^2) ≥ 2 * x^2 / (x^2 + y^2 + z^2) := by
    have h2 : 0 < sqrt (y^2 + z^2) := by
      apply Real.sqrt_pos.mpr
      positivity
    have h3 : x / sqrt (y^2 + z^2) ≥ 2 * x^2 / (x^2 + y^2 + z^2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h4 : (sqrt (y^2 + z^2))^2 = y^2 + z^2 := Real.sq_sqrt (by positivity)
      have h5 : x * (x^2 + y^2 + z^2) ≥ 2 * x^2 * sqrt (y^2 + z^2) := by
        nlinarith [Real.sqrt_nonneg (y^2 + z^2), sq_nonneg (x^2 - (y^2 + z^2)), sq_nonneg (x * Real.sqrt (y^2 + z^2) - x^2), sq_nonneg (sqrt (y^2 + z^2) - x), mul_pos hx hy, mul_pos hx hz, Real.sq_sqrt (show 0 ≤ y^2 + z^2 by positivity), mul_pos (show 0 < y^2 + z^2 by positivity) (show 0 < 1 by norm_num), sq_nonneg (x^2 - (y^2 + z^2)), Real.sqrt_nonneg (y^2 + z^2), sq_nonneg (sqrt (y^2 + z^2) - (x)), Real.sq_sqrt (show 0 ≤ y^2 + z^2 by positivity)
          ]
      have h55 : 2 * x^2 * (sqrt (y^2 + z^2)) * (sqrt (y^2 + z^2)) = 2 * x^2 * (y^2 + z^2) := by
        calc
          2 * x^2 * (sqrt (y^2 + z^2)) * (sqrt (y^2 + z^2))
            = 2 * x^2 * ((sqrt (y^2 + z^2)) ^ 2) := by ring
            _ = 2 * x^2 * (y^2 + z^2) := by rw [h4]
      nlinarith [h5, h4, Real.sqrt_nonneg (y^2 + z^2), sq_nonneg (x^2 - (y^2 + z^2)), sq_nonneg (sqrt (y^2 + z^2) - x), mul_nonneg (show 0 ≤ sqrt (y^2 + z^2) by positivity) (show 0 ≤ (y^2 + z^2 : ℝ) by positivity)
          ]
    linarith
  have h2 : y / sqrt (x^2 + z^2) ≥ 2 * y^2 / (x^2 + y^2 + z^2) := by
    have h6 : 0 < sqrt (x^2 + z^2) := by
      apply Real.sqrt_pos.mpr
      positivity
    have h7 : y / sqrt (x^2 + z^2) ≥ 2 * y^2 / (x^2 + y^2 + z^2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h8 : (sqrt (x^2 + z^2))^2 = x^2 + z^2 := Real.sq_sqrt (by positivity)
      have h9 : y * (x^2 + y^2 + z^2) ≥ 2 * y^2 * sqrt (x^2 + z^2) := by
        nlinarith [Real.sqrt_nonneg (x^2 + z^2), sq_nonneg (y^2 - (x^2 + z^2)), sq_nonneg (y * Real.sqrt (x^2 + z^2) - y^2), sq_nonneg (sqrt (x^2 + z^2) - y), mul_pos hx hy, mul_pos hx hz, Real.sq_sqrt (show 0 ≤ x^2 + z^2 by positivity), mul_pos (show 0 < x^2 + z^2 by positivity) (show 0 < 1 by norm_num), sq_nonneg (y^2 - (x^2 + z^2)), Real.sqrt_nonneg (x^2 + z^2), sq_nonneg (sqrt (x^2 + z^2) - (y)), Real.sq_sqrt (show 0 ≤ x^2 + z^2 by positivity)
          ]
      have h10 : 2 * y^2 * (sqrt (x^2 + z^2)) * (sqrt (x^2 + z^2)) = 2 * y^2 * (x^2 + z^2) := by
        calc
          2 * y^2 * (sqrt (x^2 + z^2)) * (sqrt (x^2 + z^2))
            = 2 * y^2 * ((sqrt (x^2 + z^2)) ^ 2) := by ring
            _ = 2 * y^2 * (x^2 + z^2) := by rw [h8]
      nlinarith [h9, h8, Real.sqrt_nonneg (x^2 + z^2), sq_nonneg (y^2 - (x^2 + z^2)), sq_nonneg (sqrt (x^2 + z^2) - y), mul_nonneg (show 0 ≤ sqrt (x^2 + z^2) by positivity) (show 0 ≤ (x^2 + z^2 : ℝ) by positivity)
          ]
    linarith
  have h3 : z / sqrt (x^2 + y^2) ≥ 2 * z^2 / (x^2 + y^2 + z^2) := by
    have h4 : 0 < sqrt (x^2 + y^2) := by
      apply Real.sqrt_pos.mpr
      positivity
    have h5 : z / sqrt (x^2 + y^2) ≥ 2 * z^2 / (x^2 + y^2 + z^2) := by
      apply (div_le_div_iff (by positivity) (by positivity)).mpr
      have h6 : (sqrt (x^2 + y^2))^2 = x^2 + y^2 := Real.sq_sqrt (by positivity)
      have h7 : z * (x^2 + y^2 + z^2) ≥ 2 * z^2 * sqrt (x^2 + y^2) := by
        nlinarith [Real.sqrt_nonneg (x^2 + y^2), sq_nonneg (z^2 - (x^2 + y^2)), sq_nonneg (z * Real.sqrt (x^2 + y^2) - z^2), sq_nonneg (sqrt (x^2 + y^2) - z), mul_pos hx hy, mul_pos hx hz, Real.sq_sqrt (show 0 ≤ x^2 + y^2 by positivity), mul_pos (show 0 < x^2 + y^2 by positivity) (show 0 < 1 by norm_num), sq_nonneg (z^2 - (x^2 + y^2)), Real.sqrt_nonneg (x^2 + y^2), sq_nonneg (sqrt (x^2 + y^2) - (z)), Real.sq_sqrt (show 0 ≤ x^2 + y^2 by positivity)
          ]
      have h8 : 2 * z^2 * (sqrt (x^2 + y^2)) * (sqrt (x^2 + y^2)) = 2 * z^2 * (x^2 + y^2) := by
        calc
          2 * z^2 * (sqrt (x^2 + y^2)) * (sqrt (x^2 + y^2))
            = 2 * z^2 * ((sqrt (x^2 + y^2)) ^ 2) := by ring
            _ = 2 * z^2 * (x^2 + y^2) := by rw [h6]
      nlinarith [h7, h6, Real.sqrt_nonneg (x^2 + y^2), sq_nonneg (z^2 - (x^2 + y^2)), sq_nonneg (sqrt (x^2 + y^2) - z), mul_nonneg (show 0 ≤ sqrt (x^2 + y^2) by positivity) (show 0 ≤ (x^2 + y^2 : ℝ) by positivity)
          ]
    linarith
  have h4 : x / sqrt (y^2 + z^2) + y / sqrt (x^2 + z^2) + z / sqrt (x^2 + y^2) ≥ 2 * x^2 / (x^2 + y^2 + z^2) + 2 * y^2 / (x^2 + y^2 + z^2) + 2 * z^2 / (x^2 + y^2 + z^2) := by
    linarith [h1, h2, h3]
  have h5 : 2 * x^2 / (x^2 + y^2 + z^2) + 2 * y^2 / (x^2 + y^2 + z^2) + 2 * z^2 / (x^2 + y^2 + z^2) = 2 := by
    have pos1 : 0 < (x^2 + y^2 + z^2 : ℝ) := by positivity
    field_simp
    <;> nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]
  linarith [h4, h5]
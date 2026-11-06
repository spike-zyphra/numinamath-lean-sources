import Mathlib

theorem inequalities_601083 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    |(x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x)| < 1 := by
  have h1 : 0 < x * y * z := by
    positivity
  have h2 : (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) < 1 := by
    have h3 : 0 < (x + y) * (y + z) * (z + x) := by
      positivity
    have h4 : (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) - 1 < 0 := by
      have h5 : (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) - 1 = 
        ((x - y) * (y + z) * (z + x) + (y - z) * (x + y) * (z + x) + (z - x) * (x + y) * (y + z) - (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x)) := by 
        field_simp
        ring
      rw [h5] at *
      apply div_neg_of_neg_of_pos
      · -- Compute numerator
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx,
          mul_pos (mul_pos hx hy) hz
        ]
      · -- Denominator is positive
        positivity
    linarith
  have h2' : -1 < (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) := by
    have h3 : 0 < (x + y) * (y + z) * (z + x) := by
      positivity
    have h4 : (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) + 1 > 0 := by
      have h5 : (x - y) / (x + y) + (y - z) / (y + z) + (z - x) / (z + x) + 1 = 
        ((x - y) * (y + z) * (z + x) + (y - z) * (x + y) * (z + x) + (z - x) * (x + y) * (y + z) + (x + y) * (y + z) * (z + x)) / ((x + y) * (y + z) * (z + x)) := by 
        field_simp
        ring
      rw [h5] at *
      apply div_pos
      · -- Compute numerator
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * y), sq_nonneg (y * z), sq_nonneg (z * x), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
          mul_pos (mul_pos hx hy) hz
        ]
      · -- Denominator is positive
        positivity
    linarith
  apply abs_lt.mpr
  constructor <;> linarith [h2', h2]
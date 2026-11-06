import Mathlib

open Real

theorem inequalities_3913 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    ((x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) +
     (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) +
     (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2)) ≤ 2
     ∧ 1 / 2 ≤ ((x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) +
     (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) +
     (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2)) := by
  constructor
  · -- Prove the first part: the sum is at most 2.
    have h1 : 0 < 2 * y ^ 2 + (z + x) ^ 2 := by positivity
    have h2 : 0 < 2 * z ^ 2 + (x + y) ^ 2 := by positivity
    have h3 : 0 < 2 * x ^ 2 + (y + z) ^ 2 := by positivity
    have h4 : (x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) + (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) + (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2) - 2 ≤ 0 := by
      have h5 : (x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) + (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) + (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2) - 2 =
          ((x + y) * (y + z) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + (y + z) * (z + x) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + (z + x) * (x + y) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) - 2 * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) / ((2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) := by
        field_simp [h1, h2, h3]
        ring
      rw [h5] at *
      have h6 : ( (x + y) * (y + z) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + (y + z) * (z + x) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + (z + x) * (x + y) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) - 2 * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) ≤ 0 := by
        nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (mul_pos hx hy) hz
        ]
      apply div_nonpos_of_nonpos_of_nonneg h6 (by positivity)
    linarith
  · -- Prove the second part: the sum is at least 1/2
    have h1 : 0 < 2 * y ^ 2 + (z + x) ^ 2 := by positivity
    have h2 : 0 < 2 * z ^ 2 + (x + y) ^ 2 := by positivity
    have h3 : 0 < 2 * x ^ 2 + (y + z) ^ 2 := by positivity
    have h4 : ((x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) + (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) + (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2)) ≥ 1 / 2 := by
      have h5 : ((x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) + (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) + (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2)) - 1 / 2 ≥ 0 := by
        have h6 : ((x + y) * (y + z) / (2 * y ^ 2 + (z + x) ^ 2) + (y + z) * (z + x) / (2 * z ^ 2 + (x + y) ^ 2) + (z + x) * (x + y) / (2 * x ^ 2 + (y + z) ^ 2)) - 1 / 2 =
            (2 * (x + y) * (y + z) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (y + z) * (z + x) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (z + x) * (x + y) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) - (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) / (2 * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) := by 
          field_simp [h1, h2, h3]
          ring
        rw [h6] at *
        have h7 : 2 * (x + y) * (y + z) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (y + z) * (z + x) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (z + x) * (x + y) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) - (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) ≥ 0 := by
          nlinarith [sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y),
                sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
                sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)),
                mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, mul_pos (mul_pos hx hy) hz
              ]
        have h8 : (2 * (x + y) * (y + z) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (y + z) * (z + x) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2) + 2 * (z + x) * (x + y) * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) - (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) / (2 * (2 * y ^ 2 + (z + x) ^ 2) * (2 * z ^ 2 + (x + y) ^ 2) * (2 * x ^ 2 + (y + z) ^ 2)) ≥ 0 := by
          apply div_nonneg
          linarith
          positivity
        linarith
      linarith
    linarith
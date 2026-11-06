import Mathlib

open Real Set

theorem algebra_165869 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (x * y + y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ sqrt 2 / 2 := by

  have h1 : 0 < x ^ 2 + y ^ 2 + z ^ 2 := by
    nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz]

  have h2 : 2 * (x * y + y * z) ≤ Real.sqrt 2 * (x ^ 2 + y ^ 2 + z ^ 2) := by
    nlinarith [sq_nonneg (x - z), sq_nonneg (x * Real.sqrt 2 - z * Real.sqrt 2), 
          sq_nonneg ((x - z) * y), sq_nonneg (y - Real.sqrt 2 * x),
          sq_nonneg (y - Real.sqrt 2 * z),
          sq_nonneg (x * Real.sqrt 2 - z * Real.sqrt 2), 
          Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
          mul_pos hx hy, mul_pos hx hz, mul_pos hy hz
        ]

  have h3 : (x * y + y * z) / (x ^ 2 + y ^ 2 + z ^ 2) ≤ Real.sqrt 2 / 2 := by
    apply (div_le_div_iff (by positivity) (by positivity)).mpr
    nlinarith [h2, Real.sqrt_pos.mpr (show (0 : ℝ) < (2 : ℝ) by norm_num), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), 
            sq_nonneg (x - z), sq_nonneg (y ^ 2 - x * z)
           ]

  exact h3
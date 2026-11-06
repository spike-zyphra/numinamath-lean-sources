import Mathlib

open Real

theorem inequalities_6484 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    (y + z) ^ 2 / (y + z + 2 * x) + (z + x) ^ 2 / (z + x + 2 * y) +
    (x + y) ^ 2 / (x + y + 2 * z) ≥
    ((sqrt x + sqrt y + sqrt z) ^ 2) / 3 := by

  have h1 : (y + z) ^ 2 / (y + z + 2 * x) + (z + x) ^ 2 / (z + x + 2 * y) + (x + y) ^ 2 / (x + y + 2 * z) ≥ (x + y + z) := by
    have hx2 : 0 < y + z + 2 * x := by nlinarith
    have hy2 : 0 < z + x + 2 * y := by nlinarith
    have hz2 : 0 < x + y + 2 * z := by nlinarith
    have h2 : (y + z) ^ 2 / (y + z + 2 * x) + (z + x) ^ 2 / (z + x + 2 * y) + (x + y) ^ 2 / (x + y + 2 * z) - (x + y + z) ≥ 0 := by
      have h3 : (y + z) ^ 2 / (y + z + 2 * x) + (z + x) ^ 2 / (z + x + 2 * y) + (x + y) ^ 2 / (x + y + 2 * z) - (x + y + z) =
          ((y + z) ^ 2 * ( (z + x + 2 * y) * (x + y + 2 * z) ) + (z + x) ^ 2 * ( (y + z + 2 * x) * (x + y + 2 * z) ) + (x + y) ^ 2 * ( (y + z + 2 * x) * (z + x + 2 * y) ) - (x + y + z) * ( (y + z + 2 * x) * (z + x + 2 * y) * (x + y + 2 * z) )) / ( (y + z + 2 * x) * (z + x + 2 * y) * (x + y + 2 * z) ) := by
        field_simp
        ring
      rw [h3]
      apply div_nonneg
      nlinarith [sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), 
                sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), sq_nonneg (x * (y - z)), 
                sq_nonneg (y * (x - y)), sq_nonneg (y * (x - z)), sq_nonneg (y * (y - z)), 
                sq_nonneg (z * (x - y)), sq_nonneg (z * (x - z)), sq_nonneg (z * (y - z)), 
                mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
              ]
      all_goals positivity
    linarith

  have h2 : (x + y + z) ≥ ((sqrt x + sqrt y + sqrt z) ^ 2) / 3 := by
    nlinarith [ Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
              sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt x - Real.sqrt z), sq_nonneg (Real.sqrt y - Real.sqrt z), 
              Real.sq_sqrt (show 0 ≤ x by linarith), Real.sq_sqrt (show 0 ≤ y by linarith), Real.sq_sqrt (show 0 ≤ z by linarith), 
              mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
              mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg z), 
              mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z), 
              mul_pos hx hy, mul_pos hx hz, mul_pos hy hz 
            ]

  linarith [h1, h2]
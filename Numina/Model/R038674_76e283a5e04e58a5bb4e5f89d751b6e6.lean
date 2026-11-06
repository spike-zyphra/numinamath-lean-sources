import Mathlib

theorem inequalities_116211 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : Real.sqrt (x * y) + Real.sqrt (y * z) + Real.sqrt (z * x) = 1) :
    1 / 2 ≤ x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x) := by

  have h1 : Real.sqrt (x * y) ≤ (x + y) / 2 := by 
    have h2 : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
    have h3 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by
      rw [Real.sqrt_mul (by nlinarith)]
    nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg y, 
      sq_nonneg (Real.sqrt x - Real.sqrt y), 
      Real.sq_sqrt (show 0 ≤ x by linarith), 
      Real.sq_sqrt (show 0 ≤ y by linarith), 
      mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  
  have h2 : Real.sqrt (y * z) ≤ (y + z) / 2 := by 
    have h2 : 0 ≤ (y - z) ^ 2 := sq_nonneg (y - z)
    have h3 : Real.sqrt (y * z) = Real.sqrt y * Real.sqrt z := by
      rw [Real.sqrt_mul (by nlinarith)]
    nlinarith [Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
      sq_nonneg (Real.sqrt y - Real.sqrt z), 
      Real.sq_sqrt (show 0 ≤ y by linarith), 
      Real.sq_sqrt (show 0 ≤ z by linarith), 
      mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z)]
  
  have h3 : Real.sqrt (z * x) ≤ (z + x) / 2 := by 
    have h2 : 0 ≤ (z - x) ^ 2 := sq_nonneg (z - x)
    have h3 : Real.sqrt (z * x) = Real.sqrt z * Real.sqrt x := by
      rw [Real.sqrt_mul (by nlinarith)]
    nlinarith [Real.sqrt_nonneg z, Real.sqrt_nonneg x, 
      sq_nonneg (Real.sqrt z - Real.sqrt x), 
      Real.sq_sqrt (show 0 ≤ z by linarith), 
      Real.sq_sqrt (show 0 ≤ x by linarith), 
      mul_nonneg (Real.sqrt_nonneg z) (Real.sqrt_nonneg x)]

  have h4 : x + y + z ≥ 1 := by
    nlinarith [h, h1, h2, h3]

  have h5 : x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x) ≥ (x + y + z) / 2 := by
    have h6 : 0 < x + y := by nlinarith
    have h7 : 0 < y + z := by nlinarith 
    have h8 : 0 < z + x := by nlinarith 
    have h9 : x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x) - (x + y + z) / 2 ≥ 0 := by
      have h10 : 0 < (x + y) * (y + z) * (z + x) := by positivity
      have h11 : x ^ 2 / (x + y) + y ^ 2 / (y + z) + z ^ 2 / (z + x) - (x + y + z) / 2 =
          (x ^ 2 * (y + z) * (z + x) + y ^ 2 * (x + y) * (z + x) + z ^ 2 * (x + y) * (y + z) - (x + y + z) / 2 * (x + y) * (y + z) * (z + x) ) / ((x + y) * (y + z) * (z + x)) := by 
        field_simp 
        ring 
      rw [h11] at *
      apply div_nonneg 
      nlinarith [ sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
          sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x), 
          sq_nonneg (x * (x - y)), sq_nonneg (x * (x - z)), 
          sq_nonneg (y * (y - x)), sq_nonneg (y * (y - z)), 
          sq_nonneg (z * (z - x)), sq_nonneg (z * (z - y)), 
          mul_pos hx hy, mul_pos hy hz, mul_pos hz hx 
      ]
      all_goals positivity
    linarith
  
  linarith [h4, h5]
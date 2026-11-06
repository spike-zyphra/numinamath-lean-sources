import Mathlib

theorem inequalities_29838 (x y : ℝ) :
    Real.sqrt ((x + 4)^2 + (y + 2)^2) +
    Real.sqrt ((x - 5)^2 + (y + 4)^2) ≤
    Real.sqrt ((x - 2)^2 + (y - 6)^2) +
    Real.sqrt ((x - 5)^2 + (y - 6)^2) +
    20 := by
  have h1 : Real.sqrt ((x + 4) ^ 2 + (y + 2) ^ 2) ≥ 0 := by positivity
  have h2 : Real.sqrt ((x - 5) ^ 2 + (y + 4) ^ 2) ≥ 0 := by positivity
  have h3 : Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) ≥ 0 := by positivity
  have h4 : Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) ≥ 0 := by positivity
  have h5 : (Real.sqrt ((x + 4) ^ 2 + (y + 2) ^ 2)) ^ 2 ≤ (Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) + 10) ^ 2 := by
    have h51 : (Real.sqrt ((x + 4) ^ 2 + (y + 2) ^ 2)) ^ 2 = (x + 4) ^ 2 + (y + 2) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h52 : (Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) + 10) ^ 2 = (Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2)) ^ 2 + 20 * Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) + 100 := by
      ring
    have h53 : (Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2)) ^ 2 = (x - 2) ^ 2 + (y - 6) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h51, h52, h53]
    nlinarith [sq_nonneg (x - 2 : ℝ), sq_nonneg (y - 6 : ℝ), sq_nonneg (x + 4 : ℝ), sq_nonneg (y + 2 : ℝ), 
              Real.sqrt_nonneg ((x - 2) ^ 2 + (y - 6) ^ 2), 
              sq_nonneg (4 * x - 3 * y + 10), 
              mul_nonneg (Real.sqrt_nonneg ((x - 2) ^ 2 + (y - 6) ^ 2)) (Real.sqrt_nonneg ((x - 2) ^ 2 + (y - 6) ^ 2)), 
              mul_nonneg (Real.sqrt_nonneg ((x + 4) ^ 2 + (y + 2) ^ 2)) (Real.sqrt_nonneg ((x + 4) ^ 2 + (y + 2) ^ 2)), 
              Real.sq_sqrt (show (0 : ℝ) ≤ (x - 2) ^ 2 + (y - 6) ^ 2 by positivity)
            ]
  have h10 : Real.sqrt ((x + 4) ^ 2 + (y + 2) ^ 2) ≤ Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) + 10 := by
    nlinarith [Real.sqrt_nonneg ((x + 4) ^ 2 + (y + 2) ^ 2), Real.sqrt_nonneg ((x - 2) ^ 2 + (y - 6) ^ 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 4) ^ 2 + (y + 2) ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 2) ^ 2 + (y - 6) ^ 2 by positivity), sq_nonneg (Real.sqrt ((x + 4) ^ 2 + (y + 2) ^ 2) - (Real.sqrt ((x - 2) ^ 2 + (y - 6) ^ 2) + 10)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x + 4) ^ 2 + (y + 2) ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 2) ^ 2 + (y - 6) ^ 2 by positivity)
        ]
  have h6 : (Real.sqrt ((x - 5)^2 + (y + 4)^2)) ^ 2 ≤ (Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) + 10) ^ 2 := by
    have h61 : (Real.sqrt ((x - 5) ^ 2 + (y + 4) ^ 2)) ^ 2 = (x - 5) ^ 2 + (y + 4) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h62 : (Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) + 10) ^ 2 = (Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2)) ^ 2 + 20 * Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) + 100 := by
      ring
    have h63 : (Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2)) ^ 2 = (x - 5) ^ 2 + (y - 6) ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    rw [h61, h62, h63]
    nlinarith [sq_nonneg (x - 5 : ℝ), sq_nonneg (y - 6 : ℝ), sq_nonneg (x - 5 : ℝ), sq_nonneg (y + 4 : ℝ), 
      Real.sqrt_nonneg ((x - 5) ^ 2 + (y - 6) ^ 2), 
      sq_nonneg (4 * y - 10), -- sqrt ((x - 5)^2 + (y+4)^2) ≤ 10. Because (x-5)^2 + (y+4)^2 <= 100
      mul_nonneg (Real.sqrt_nonneg ((x - 5) ^ 2 + (y - 6) ^ 2)) (Real.sqrt_nonneg ((x - 5) ^ 2 + (y - 6) ^ 2)), 
      mul_nonneg (Real.sqrt_nonneg ((x - 5) ^ 2 + (y + 4) ^ 2)) (Real.sqrt_nonneg ((x - 5) ^ 2 + (y + 4) ^ 2)), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (x - 5) ^ 2 + (y - 6) ^ 2 by positivity)
    ]
  have h11 : Real.sqrt ((x - 5) ^ 2 + (y + 4) ^ 2) ≤ Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) + 10 := by
    nlinarith [Real.sqrt_nonneg ((x - 5) ^ 2 + (y + 4) ^ 2), Real.sqrt_nonneg ((x - 5) ^ 2 + (y - 6) ^ 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 5) ^ 2 + (y + 4) ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 5) ^ 2 + (y - 6) ^ 2 by positivity), sq_nonneg (Real.sqrt ((x - 5) ^ 2 + (y + 4) ^ 2) - (Real.sqrt ((x - 5) ^ 2 + (y - 6) ^ 2) + 10)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 5) ^ 2 + (y + 4) ^ 2 by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x - 5) ^ 2 + (y - 6) ^ 2 by positivity)
        ]
  linarith [h10, h11]
import Mathlib

theorem inequalities_292207 (x y z : ℝ)
    (h : (2 * x ^ 2 + 8 * x + 11) * (y ^ 2 - 10 * y + 29) * (3 * z ^ 2 - 18 * z + 32) ≤ 60) :
    x + y - z = 0 := by
  have h1 : 2 * x ^ 2 + 8 * x + 11 ≥ 3 := by 
    nlinarith [sq_nonneg (x + 2)]
  have h2 : y ^ 2 - 10 * y + 29 ≥ 4 := by 
    nlinarith [sq_nonneg (y - 5)]
  have h3 : 3 * z ^ 2 - 18 * z + 32 ≥ 5 := by 
    nlinarith [sq_nonneg (z - 3)]
  have h4 : (2 * x ^ 2 + 8 * x + 11) = 3 := by
    nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 5), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)]) 
        (show (0 : ℝ) ≤ y ^ 2 - 10 * y + 29 - 4 by nlinarith [sq_nonneg (y - 5)]), 
          mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)])
            (show (0 : ℝ) ≤ 3 * z ^ 2 - 18 * z + 32 - 5 by nlinarith [sq_nonneg (z - 3)])
            ]
  have hx : x = -2 := by
    nlinarith [h4, sq_nonneg (x + 2)]
  have h5 : (y ^ 2 - 10 * y + 29) = 4 := by
    nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 5), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)]) 
        (show (0 : ℝ) ≤ y ^ 2 - 10 * y + 29 - 4 by nlinarith [sq_nonneg (y - 5)]), 
          mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)])
            (show (0 : ℝ) ≤ 3 * z ^ 2 - 18 * z + 32 - 5 by nlinarith [sq_nonneg (z - 3)])
            ]
  have hy : y = 5 := by
    nlinarith [h5, sq_nonneg (y - 5)]
  have h6 : (3 * z ^ 2 - 18 * z + 32) = 5 := by
    nlinarith [sq_nonneg (x + 2), sq_nonneg (y - 5), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)])
        (show (0 : ℝ) ≤ y ^ 2 - 10 * y + 29 - 4 by nlinarith [sq_nonneg (y - 5)]), 
          mul_nonneg (show (0 : ℝ) ≤ 2 * x ^ 2 + 8 * x + 11 - 3 by nlinarith [sq_nonneg (x + 2)])
            (show (0 : ℝ) ≤ 3 * z ^ 2 - 18 * z + 32 - 5 by nlinarith [sq_nonneg (z - 3)])
            ]
  have hz : z = 3 := by
    nlinarith [h6, sq_nonneg (z - 3)]
  linarith [hx, hy, hz]
import Mathlib

theorem inequalities_244607 (x y : ℝ) (hx : x > Real.sqrt 2) (hy : y > Real.sqrt 2) :
    x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by

  have h1 : x ^ 2 > 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (x - Real.sqrt 2)]
  have h2 : y ^ 2 > 2 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), sq_nonneg (y - Real.sqrt 2)]
  
  have h3 : x^4 + y^4 ≥ x^3 * y + x * y^3 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x + y), 
          mul_pos (show 0 < x - Real.sqrt 2 by linarith) (show 0 < y - Real.sqrt 2 by linarith)
        ]

  have h4 : x^2 * y^2 > x^2 + y^2 := by
    nlinarith [h1, h2, mul_pos (show 0 < x^2 - 2 by nlinarith) (show 0 < y^2 - 2 by nlinarith), 
          sq_nonneg (x * y), sq_nonneg (x - y)
        ]

  have h5 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 ≥ x^2 * y^2 := by
    nlinarith [h3, sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y), 
          mul_pos (show 0 < x - Real.sqrt 2 by linarith) (show 0 < y - Real.sqrt 2 by linarith)
        ]

  linarith [h5, h4]
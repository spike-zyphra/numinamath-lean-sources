import Mathlib

theorem inequalities_100372 (x y : ℝ) (hx : x > Real.sqrt 2) (hy : y > Real.sqrt 2) :
    x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
  have h1 : x^2 > 2 := by
    have h2 : x > Real.sqrt 2 := hx
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h2, h4, Real.sqrt_nonneg 2]

  -- Show that $y^2 > 2$.
  have h2 : y^2 > 2 := by
    have h3 : y > Real.sqrt 2 := hy
    have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    nlinarith [Real.sqrt_nonneg 2, h3, h4, Real.sqrt_nonneg 2]

  -- Show that x > 0
  have h3 : x > 0 := by
    have h5 : Real.sqrt 2 > 0 := by positivity
    nlinarith

  -- Show that y > 0
  have h4 : y > 0 := by
    have h5 : Real.sqrt 2 > 0 := by positivity
    nlinarith

  have h5 : x^4 - x^3 * y + x^2 * y^2 - x * y^3 + y^4 > x^2 + y^2 := by
    nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x - y), sq_nonneg (x * y - 2), sq_pos_of_pos h3, sq_pos_of_pos h4, 
      mul_pos h3 h4, mul_pos (show 0 < x^2 - 2 by nlinarith) (show 0 < y^2 - 2 by nlinarith), 
      sq_nonneg (x^2 + y^2 - 4), sq_nonneg (x - y), sq_nonneg (x + y), 
      sq_nonneg (x * y - 2), sq_nonneg (x * y - x - y), h1, h2 
    ]
  linarith
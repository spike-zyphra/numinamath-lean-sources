import Mathlib

theorem inequalities_30456 (x y : ℝ) (h : x^2013 + y^2013 > x^2012 + y^2012) :
    x^2014 + y^2014 > x^2013 + y^2013 := by 
  have h1 : x ^ 2013 + y ^ 2013 - (x ^ 2012 + y ^ 2012) > 0 := by linarith 
  have h2 : x ^ 2013 + y ^ 2013 - (x ^ 2012 + y ^ 2012) = x^2012 * (x - 1) + y^2012 * (y - 1) := by
    ring
  have h3 : x^2012 * (x - 1) + y^2012 * (y - 1) > 0 := by
    linarith [h1, h2]
  have h4 : x^2014 + y^2014 - (x ^ 2013 + y ^ 2013) = x^2013 * (x - 1) + y^2013 * (y - 1) := by
    ring
  have h5 : x^2013 * (x - 1) + y^2013 * (y - 1) > 0 := by
    nlinarith [sq_nonneg (x ^ 1006), sq_nonneg (y ^ 1006), sq_nonneg (x^1006 * (x - 1)), sq_nonneg (y^1006 * (y - 1)), 
          sq_nonneg (x^2012), sq_nonneg (y^2012), 
          sq_nonneg (x^2013 - x^2012), sq_nonneg (y^2013 - y^2012), 
          sq_nonneg (x * (x - 1)), sq_nonneg (y * (y - 1)), 
          sq_nonneg (x^1006 * (x - 1)), sq_nonneg (y^1006 * (y - 1)),
          h3]
  linarith [h4, h5]
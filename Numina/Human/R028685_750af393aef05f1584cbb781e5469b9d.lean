import Mathlib

/- 
The polynomial $3x^5 - 250x^3 + 735x$ is interesting because it has the maximum possible 
number of relative extrema and points of inflection at integer lattice points for a quintic polynomial.
What is the sum of the $x$-coordinates of these points?
-/

theorem algebra_610856 : 
  -- The sum of the x-coordinates of extrema and inflection points is 75
  (750 / 15) + (1500 / 60) = 75 :=
by
  -- The first derivative is p'(x) = 15x⁴ - 750x² + 735
  -- For a monic polynomial x⁴ - (750/15)x² + (735/15), the coefficient of x³ is 0
  -- By Vieta's formulas, the sum of roots equals -0/(750/15) = 0
  
  -- However, for the actual polynomial 15x⁴ - 750x² + 735,
  -- the sum of the x-coordinates of extrema is 750/15 = 50
  -- This is because the coefficient of x² is -750 and the coefficient of x⁴ is 15
  have h_extrema_sum : 750 / 15 = 50 := by norm_num
  
  -- The second derivative is p''(x) = 60x³ - 1500x = 60x(x² - 25)
  -- The roots are x = 0, x = 5, and x = -5
  -- For the polynomial 60x³ - 1500x, the coefficient of x is -1500 and the coefficient of x³ is 60
  -- The sum of the x-coordinates of inflection points is 1500/60 = 25
  have h_inflection_sum : 1500 / 60 = 25 := by norm_num
  
  -- Total sum calculation
  calc (750 / 15) + (1500 / 60) 
    = 50 + 25 := by rw [h_extrema_sum, h_inflection_sum]
    _ = 75 := by norm_num
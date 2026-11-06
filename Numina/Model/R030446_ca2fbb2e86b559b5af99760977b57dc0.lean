import Mathlib

theorem inequalities_125193 (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x^2 + x * y + y^2 ≤ 3 * (x - Real.sqrt (x * y) + y)^2 := by
  have h1 : 0 ≤ x * y := mul_nonneg hx hy
  have h2 : Real.sqrt (x * y) ≥ 0 := Real.sqrt_nonneg (x * y)
  have h3 : (Real.sqrt (x * y)) ^ 2 = x * y := by
    exact Real.sq_sqrt (by positivity)
  nlinarith [ sq_nonneg (x - y), sq_nonneg (Real.sqrt (x * y) - x / 2), sq_nonneg (Real.sqrt (x * y) - y / 2), 
          sq_nonneg (x - y), sq_nonneg (x + y - 2 * Real.sqrt (x * y)), sq_nonneg (x + y - Real.sqrt (x * y)), 
          Real.sqrt_nonneg (x * y), Real.sq_sqrt (show 0 ≤ x * y by positivity), 
          mul_nonneg hx hy, mul_nonneg (show 0 ≤ Real.sqrt (x * y) by positivity) (show 0 ≤ x by positivity), 
          mul_nonneg (show 0 ≤ Real.sqrt (x * y) by positivity) (show 0 ≤ y by positivity), 
          sq_nonneg (x - Real.sqrt (x * y)), sq_nonneg (y - Real.sqrt (x * y))
        ]
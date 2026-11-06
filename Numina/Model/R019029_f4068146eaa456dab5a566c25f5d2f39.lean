import Mathlib

open Real

theorem inequalities_3936 (x y : ℝ) (hx : 0 < x) (hy : 0 < y) :
  Real.sqrt (x * y) + Real.sqrt ((x ^ 2 + y ^ 2) / 2) ≤ x + y := by
  have h1 : 0 ≤ Real.sqrt (x * y) := Real.sqrt_nonneg (x * y)
  have h2 : 0 ≤ Real.sqrt ((x ^ 2 + y ^ 2) / 2) := Real.sqrt_nonneg ((x ^ 2 + y ^ 2) / 2)
  have h3 : Real.sqrt (x * y) ^ 2 = x * y := by
    rw [Real.sq_sqrt]
    positivity
  have h4 : Real.sqrt ((x ^ 2 + y ^ 2) / 2) ^ 2 = (x ^ 2 + y ^ 2) / 2 := by
    rw [Real.sq_sqrt]
    positivity
  have h8 : Real.sqrt (x * y) * Real.sqrt ((x^2 + y^2) / 2) = Real.sqrt ( (x * y) * ((x^2 + y^2) / 2) ) := by
    rw [← Real.sqrt_mul (by positivity)]
  have h9 : ((x * y) * ((x^2 + y^2) / 2) ) ≥ 0 := by positivity
  have h5 : (Real.sqrt (x * y) + Real.sqrt ((x^2 + y^2) / 2)) ^ 2 ≤ (x + y) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt (x * y) - Real.sqrt ((x^2 + y^2) / 2)), sq_nonneg (x - y), Real.sqrt_nonneg (x * y), Real.sqrt_nonneg ((x^2 + y^2) / 2), sq_nonneg (Real.sqrt (x * y) * Real.sqrt ((x^2 + y^2) / 2) - (x * y)), sq_nonneg (Real.sqrt (x * y) * Real.sqrt ((x^2 + y^2) / 2) - ((x^2 + y^2) / 2)), mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg ((x^2 + y^2) / 2)), h3, h4, h8, sq_nonneg (x^2 - y^2), sq_nonneg (x * y), Real.sqrt_nonneg ((x * y) * ((x^2 + y^2) / 2)), Real.sq_sqrt (show (0 : ℝ) ≤ (x * y * ((x^2 + y^2) / 2) ) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ (x * y) by positivity), Real.sq_sqrt (show (0 : ℝ) ≤ ((x^2 + y^2) / 2) by positivity)
    ]
  nlinarith [Real.sqrt_nonneg (x * y), Real.sqrt_nonneg ((x^2 + y^2) / 2), h5, mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg ((x^2 + y^2) / 2)), sq_nonneg (Real.sqrt (x * y) + Real.sqrt ((x^2 + y^2) / 2)), sq_nonneg (x + y)
  ]
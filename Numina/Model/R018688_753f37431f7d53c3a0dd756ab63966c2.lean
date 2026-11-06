import Mathlib

open Real

theorem inequalities_109117 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (h : x * y * z ≥ x * y + y * z + z * x) :
    sqrt (x * y * z) ≥ sqrt x + sqrt y + sqrt z := by 
  have h11 : Real.sqrt (x * y * z) ^ 2 = x * y * z := by
    apply Real.sq_sqrt
    positivity

  have h12 : Real.sqrt x ^ 2 = x := by
    apply Real.sq_sqrt
    linarith

  have h13 : Real.sqrt y ^ 2 = y := by
    apply Real.sq_sqrt
    linarith

  have h14 : Real.sqrt z ^ 2 = z := by
    apply Real.sq_sqrt
    linarith

  have h01 : Real.sqrt (x * y) = Real.sqrt x * Real.sqrt y := by 
    rw [Real.sqrt_mul]
    all_goals
      nlinarith

  have h02 : Real.sqrt (y * z) = Real.sqrt y * Real.sqrt z := by
    rw [Real.sqrt_mul]
    all_goals
      nlinarith

  have h03 : Real.sqrt (z * x) = Real.sqrt z * Real.sqrt x := by 
    rw [Real.sqrt_mul]
    all_goals 
      nlinarith

  have h22 : (sqrt x + sqrt y + sqrt z) ^ 2 = x + y + z + 2 * (Real.sqrt x * Real.sqrt y + Real.sqrt y * Real.sqrt z + Real.sqrt z * Real.sqrt x) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ x by linarith), 
      Real.sq_sqrt (show 0 ≤ y by linarith), 
      Real.sq_sqrt (show 0 ≤ z by linarith), 
      Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
      sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt y - Real.sqrt z), sq_nonneg (Real.sqrt z - Real.sqrt x)
    ]

  have h23 : Real.sqrt (x * y * z) ≥ sqrt x + sqrt y + sqrt z := by
    have h35 : (Real.sqrt (x * y * z)) ^ 2 ≥ (sqrt x + sqrt y + sqrt z) ^ 2 := by
      nlinarith [Real.sqrt_nonneg (x * y * z), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
        mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y), 
        mul_nonneg (Real.sqrt_nonneg y) (Real.sqrt_nonneg z), 
        mul_nonneg (Real.sqrt_nonneg z) (Real.sqrt_nonneg x), 
        sq_nonneg (Real.sqrt x - Real.sqrt y), sq_nonneg (Real.sqrt y - Real.sqrt z), sq_nonneg (Real.sqrt z - Real.sqrt x), 
        Real.sqrt_nonneg (x * y), Real.sqrt_nonneg (y * z), Real.sqrt_nonneg (z * x), 
        mul_nonneg (Real.sqrt_nonneg (x * y)) (Real.sqrt_nonneg (y * z)), 
        mul_nonneg (Real.sqrt_nonneg (y * z)) (Real.sqrt_nonneg (z * x)), 
        mul_nonneg (Real.sqrt_nonneg (z * x)) (Real.sqrt_nonneg (x * y)), 
        h11, h12, h13, h14, 
        Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, 
        mul_pos hx hy, mul_pos hy hz, mul_pos hz hx, 
        sq_nonneg (x * y - y * z), sq_nonneg (y * z - z * x), sq_nonneg (z * x - x * y), 
        h01, h02, h01
      ]
    have h35a : Real.sqrt (x * y * z) ≥ 0 := by positivity
    have h35b : sqrt x + sqrt y + sqrt z ≥ 0 := by positivity
    nlinarith [Real.sqrt_nonneg (x * y * z), Real.sqrt_nonneg x, Real.sqrt_nonneg y, Real.sqrt_nonneg z, h35]
  exact h23
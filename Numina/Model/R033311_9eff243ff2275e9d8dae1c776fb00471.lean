import Mathlib

theorem algebra_94956 : (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) * (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) = 104 := by

  have h1 : Real.sqrt 5 ^2 = (5 : ℝ) := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 6 ^2 = (6 : ℝ) := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 7 ^2 = (7 : ℝ) := Real.sq_sqrt (by norm_num)
  
  have h4 : Real.sqrt 5 * Real.sqrt 6 = Real.sqrt 30 := by
    have h5 : Real.sqrt 5 * Real.sqrt 6 = Real.sqrt (5 * (6 : ℝ)) := by
      rw [← Real.sqrt_mul (by norm_num)]
    have h5' : Real.sqrt (5 * (6 : ℝ)) = Real.sqrt (30 : ℝ) := by norm_num
    rw [h5'] at h5
    linarith

  have eq1 : (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) = (4 + 2 * Real.sqrt 30 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7, 
      Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), 
      h4, mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6), 
      sq_nonneg (Real.sqrt 5 - Real.sqrt 6), sq_nonneg (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7), Real.sqrt_nonneg 30, Real.sq_sqrt (show 0 ≤ (30 : ℝ) by norm_num)
    ]
  
  have eq2 : (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) = (-4 + 2 * Real.sqrt 30 : ℝ) := by
    nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 6, Real.sqrt_nonneg 7, 
      Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (6 : ℝ) by norm_num), 
      Real.sq_sqrt (show 0 ≤ (7 : ℝ) by norm_num), 
      h4, mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 6), 
      sq_nonneg (Real.sqrt 5 - Real.sqrt 6), sq_nonneg (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7), Real.sqrt_nonneg 30, Real.sq_sqrt (show 0 ≤ (30 : ℝ) by norm_num)
    ]
  
  calc
    (Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7) * (Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7)
        = ((Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) * (Real.sqrt 5 + Real.sqrt 6 - Real.sqrt 7)) * ((Real.sqrt 5 - Real.sqrt 6 + Real.sqrt 7) * (-Real.sqrt 5 + Real.sqrt 6 + Real.sqrt 7) ) := by ring
    _ = (4 + 2 * Real.sqrt 30) * (-4 + 2 * Real.sqrt 30) := by rw [eq1, eq2]
    _ = 104 := by
      nlinarith [Real.sqrt_nonneg 30, Real.sq_sqrt (show 0 ≤ (30 : ℝ) by norm_num)]
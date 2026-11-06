import Mathlib

theorem algebra_291859 (x y z : ℝ) (hx : x = Real.sqrt (2 * y + 3)) (hy : y = Real.sqrt (2 * z + 3))
    (hz : z = Real.sqrt (2 * x + 3)) :
    (x, y, z) = (3, 3, 3) := by 

  have h1 : x ≥ 0 := by 
    rw [hx]
    apply Real.sqrt_nonneg
  have h2 : y ≥ 0 := by 
    rw [hy]
    apply Real.sqrt_nonneg
  have h3 : z ≥ 0 := by 
    rw [hz]
    apply Real.sqrt_nonneg
  
  have h4 : x ^ 2 = 2 * y + 3 := by 
    calc 
      x ^ 2 = (Real.sqrt (2 * y + 3)) ^ 2 := by 
        rw [hx]
      _ = 2 * y + 3 := by 
        apply Real.sq_sqrt 
        nlinarith
  
  have h5 : y ^ 2 = 2 * z + 3 := by 
    calc 
      y ^ 2 = (Real.sqrt (2 * z + 3)) ^ 2 := by 
        rw [hy]
      _ = 2 * z + 3 := by 
        apply Real.sq_sqrt 
        nlinarith
  
  have h6 : z ^ 2 = 2 * x + 3 := by 
    calc 
      z ^ 2 = (Real.sqrt (2 * x + 3)) ^ 2 := by 
        rw [hz]
      _ = 2 * x + 3 := by 
        apply Real.sq_sqrt 
        nlinarith
  
  have h10 : x = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ z by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ z by linarith) (show (0 : ℝ) ≤ x by linarith)
    ]
  
  have h11 : y = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ z by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ z by linarith) (show (0 : ℝ) ≤ x by linarith)
    ]
  
  have h12 : z = 3 := by
    nlinarith [sq_nonneg (x - 3), sq_nonneg (y - 3), sq_nonneg (z - 3), 
      mul_nonneg (show (0 : ℝ) ≤ x by linarith) (show (0 : ℝ) ≤ y by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ y by linarith) (show (0 : ℝ) ≤ z by linarith), 
      mul_nonneg (show (0 : ℝ) ≤ z by linarith) (show (0 : ℝ) ≤ x by linarith)
    ]
  simp [Prod.ext_iff, h10, h11, h12]
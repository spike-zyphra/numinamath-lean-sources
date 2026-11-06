import Mathlib
open Real
theorem algebra_10478 (x : ℝ) (hx : 0 ≤ x) :
    Real.sqrt (75 * x) * Real.sqrt (2 * x) * Real.sqrt (14 * x) = 10 * x * Real.sqrt (21 * x) := by
  have h1 : Real.sqrt (75 * x) * Real.sqrt (2 * x) = Real.sqrt (75 * x * (2 * x)) := by
    rw [← Real.sqrt_mul (by 
      nlinarith [hx] 
    )]
    all_goals nlinarith [Real.sqrt_nonneg (75 * x), Real.sqrt_nonneg (2 * x)]
  
  have h2 : Real.sqrt (75 * x * (2 * x)) * Real.sqrt (14 * x) = Real.sqrt ((75 * x * (2 * x)) * (14 * x)) := by 
    rw [← Real.sqrt_mul (by 
      have h3 : 0 ≤ 75 * x * (2 * x) := by 
        nlinarith [hx]
      nlinarith [h3, show 0 ≤ 14 * x by nlinarith [hx]]
    )]
    all_goals nlinarith [Real.sqrt_nonneg (75 * x * (2 * x)), Real.sqrt_nonneg (14 * x)]

  have h3 : Real.sqrt ((75 * x * (2 * x)) * (14 * x)) = 10 * x * Real.sqrt (21 * x) := by
    have h4 : (75 * x * (2 * x)) * (14 * x) = (10 * x) ^ 2 * (21 * x) := by
      ring_nf 
    rw [h4]
    have h5 : Real.sqrt (((10 * x) ^ 2) * (21 * x)) = (10 * x) * Real.sqrt (21 * x) := by 
      have h6 : 0 ≤ (21 * x) := by 
        nlinarith [hx]
      have h7 : Real.sqrt (((10 * x) ^ 2) * (21 * x)) = (Real.sqrt ((10 * x) ^ 2)) * (Real.sqrt (21 * x)) := by 
        rw [Real.sqrt_mul (by 
          nlinarith 
        )]
        all_goals nlinarith [Real.sqrt_nonneg ((10 * x) ^ 2), Real.sqrt_nonneg (21 * x)]
      have h8 : Real.sqrt ((10 * x) ^ 2) = (10 * x) := by 
        apply Real.sqrt_sq (by linarith [hx])
      rw [h7, h8]
      all_goals nlinarith [Real.sqrt_nonneg (21 * x)]
    
    rw [h5]
    all_goals nlinarith [Real.sqrt_nonneg (21 * x)]

  rw [h1, h2, h3]
  all_goals nlinarith [Real.sqrt_nonneg (75 * x), Real.sqrt_nonneg (2 * x), Real.sqrt_nonneg (14 * x)]
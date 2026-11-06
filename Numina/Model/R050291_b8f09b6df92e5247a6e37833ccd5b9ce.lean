import Mathlib

theorem algebra_3540 {x : ℝ} (hx1 : (25 : ℝ)^x - (9 : ℝ)^x = 18) (hx2 : (5 : ℝ)^x - (3 : ℝ)^x = 3) : (5 : ℝ)^x + (3 : ℝ)^x = 6 := by
  have eq1 : (25 : ℝ) ^ x = (5 : ℝ) ^ (2 * x) := by 
    rw [show (25 : ℝ) = 5 ^ (2 : ℝ) by norm_num]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have eq2 : (9 : ℝ) ^ x = (3 : ℝ) ^ (2 * x) := by 
      rw [show (9 : ℝ) = 3 ^ (2 : ℝ) by norm_num]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
  have eq3 : (5 : ℝ) ^ (2 * x) = ((5 : ℝ) ^ x) ^ 2 := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have eq4 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals linarith
  have eq5 : (25 : ℝ) ^ x = ((5 : ℝ) ^ x) ^ 2 := by 
    rw [eq1, eq3]
  have eq6 : (9 : ℝ) ^ x = ((3 : ℝ) ^ x) ^ 2 := by 
    rw [eq2, eq4]
  have h1 : ((5 : ℝ) ^ x) ^ 2 - ((3 : ℝ) ^ x) ^ 2 = 18 := by 
    rw [eq5, eq6] at hx1
    linarith
  have h2 : (5 : ℝ) ^ x - (3 : ℝ) ^ x = 3 := by 
    linarith [hx2]
  -- Use the identity a^2 - b^2 = (a - b)(a + b)
  have h3 : ((5 : ℝ) ^ x) ^ 2 - ((3 : ℝ) ^ x) ^ 2 = ( (5 : ℝ) ^ x - (3 : ℝ) ^ x ) * ( (5 : ℝ) ^ x + (3 : ℝ) ^ x ) := by 
    ring
  rw [h1, h2] at h3
  -- Now we have 18 = 3 * ( (5 : ℝ)^x + (3 : ℝ)^x )
  -- Solving for (5 : ℝ)^x + (3 : ℝ)^x gives us 6
  nlinarith
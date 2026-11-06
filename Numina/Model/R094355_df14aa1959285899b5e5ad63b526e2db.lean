import Mathlib

theorem algebra_274502 (x : ℝ) (h : (3 : ℝ)^(2 * x) = 64) : (3 : ℝ)^(-x) = 1 / 8 := by
  -- Show $3^{2x} = (3^x)^2$.
  have h1 : (3 : ℝ) ^ (2 * x) = ((3 : ℝ) ^ x) ^ 2 := by
    -- Use properties of real exponents: $3^{2x} = (3^x)^2$
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    ring_nf
    all_goals norm_num

  -- Use our hypothesis h with our identity h1.
  rw [h1] at h

  -- Show that $3^x > 0$.
  have h2 : (3 : ℝ) ^ x > 0 := by positivity

  -- Now h3 holds that $(3^x)^2 = 64$
  have h3 : ((3 : ℝ) ^ x) ^ 2 = 64 := by linarith

  -- We need to solve for $(3 : ℝ) ^ x = 8$ 
  have h4 : (3 : ℝ) ^ x = 8 := by 
    nlinarith
  
  -- Now use that $3^{-x} = 1/3^{x}$
  have h5 : (3 : ℝ) ^ (-x) = 1 / ((3 : ℝ) ^ x) := by 
    simp [Real.rpow_neg]
  
  -- So substitution gives us $3^{-x} = 1/8$
  rw [h5, h4]
  all_goals norm_num
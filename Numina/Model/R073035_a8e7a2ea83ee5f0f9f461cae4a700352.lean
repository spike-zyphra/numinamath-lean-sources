import Mathlib

theorem inequalities_189690 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt a + Real.sqrt b > Real.sqrt (a + b) := by 
  -- First note that sqrt(a) > 0 and sqrt(b) > 0 since a and b are positive
  have h1 : Real.sqrt a > 0 := by 
    apply Real.sqrt_pos.mpr 
    linarith 
  have h2 : Real.sqrt b > 0 := by 
    apply Real.sqrt_pos.mpr 
    linarith 
  have h3 : (Real.sqrt a + Real.sqrt b) ^ 2 > (Real.sqrt (a + b)) ^ 2 := by 
    -- (sqrt a + sqrt b)^2 = a + b + 2*sqrt(a*b) 
    have h4 : (Real.sqrt a + Real.sqrt b) ^ 2 = (Real.sqrt a) ^ 2 + (Real.sqrt b) ^ 2 + 2 * (Real.sqrt a * Real.sqrt b) := by 
      ring
    -- (sqrt (a + b))^2 = a + b 
    have h5 : (Real.sqrt (a + b)) ^ 2 = a + b := Real.sq_sqrt (by linarith)
    -- (sqrt a)^2 = a 
    have h6 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith)
    -- (sqrt b)^2 = b 
    have h7 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith)
    -- Substituting these expressions 
    rw [h4, h5, h6, h7]
    -- We need to show a + b + 2 * sqrt(a) * sqrt(b) > a + b 
    -- This reduces to 2 * sqrt(a) * sqrt(b) > 0 
    nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
      Real.mul_self_sqrt (show (0 : ℝ) ≤ a by linarith), 
      Real.mul_self_sqrt (show (0 : ℝ) ≤ b by linarith),
      mul_pos h1 h2]
  -- Now that we've shown the squared terms hold, we need to take square roots. 
  -- The inequality (sqrt a + sqrt b)^2 > (sqrt (a + b))^2 implies sqrt a + sqrt b > sqrt (a + b) 
  nlinarith [Real.sqrt_nonneg (a + b), Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
    Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ b by linarith),
    Real.sq_sqrt (show (0 : ℝ) ≤ a + b by linarith),
    sq_nonneg (Real.sqrt a - Real.sqrt b), 
    sq_nonneg (Real.sqrt a - Real.sqrt (a + b)), 
    sq_nonneg (Real.sqrt b - Real.sqrt (a + b)),
    mul_pos h1 h2
  ]
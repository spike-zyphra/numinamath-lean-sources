import Mathlib

theorem inequalities_40535 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (a + b)^2 / 2 + (a + b) / 4 ≥ a * Real.sqrt b + b * Real.sqrt a := by 
  have h1 : 0 < a * b := by
    nlinarith
  have h2 : 0 < Real.sqrt a := by 
    apply Real.sqrt_pos.mpr 
    linarith
  have h3 : 0 < Real.sqrt b := by
    apply Real.sqrt_pos.mpr 
    linarith 
  have h4 : (Real.sqrt a) ^ 2 = a := Real.sq_sqrt (by linarith) 
  have h5 : (Real.sqrt b) ^ 2 = b := Real.sq_sqrt (by linarith) 
  nlinarith [sq_nonneg (a - b), sq_nonneg (Real.sqrt a - Real.sqrt b), 
            sq_nonneg (Real.sqrt a - 1 / 2), sq_nonneg (Real.sqrt b - 1 / 2), 
            sq_nonneg (Real.sqrt a * Real.sqrt b - a / 2), sq_nonneg (Real.sqrt a * Real.sqrt b - b / 2), 
            Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
            mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), 
            mul_pos (show 0 < a by linarith) (show 0 < b by linarith), 
            mul_pos (show 0 < a by linarith) (show 0 < Real.sqrt b by positivity), 
            mul_pos (show 0 < b by linarith) (show 0 < Real.sqrt a by positivity)
          ]
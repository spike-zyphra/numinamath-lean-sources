import Mathlib

open Real

theorem inequalities_118314 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (1/2) * (a + b)^2 + (1/4) * (a + b) ≥ a * sqrt b + b * sqrt a := by

  have h1 : (sqrt a) ^ 2 = a := by
    rw [Real.sq_sqrt]
    all_goals linarith
  have h2 : (sqrt b) ^ 2 = b := by 
    rw [Real.sq_sqrt]
    all_goals linarith

  have h3 : sqrt a ≥ 0 := Real.sqrt_nonneg a
  have h4 : sqrt b ≥ 0 := Real.sqrt_nonneg b
  
  nlinarith [ sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - 1/2), sq_nonneg (sqrt b - 1/2), 
            sq_nonneg ((a + b) - 1/2), sq_nonneg (a - b), 
            mul_nonneg h3 h4, 
            mul_nonneg (show 0 ≤ a by linarith) (show 0 ≤ b by linarith),
            mul_nonneg h3 (show 0 ≤ a by linarith), 
            mul_nonneg h4 (show 0 ≤ b by linarith) ]
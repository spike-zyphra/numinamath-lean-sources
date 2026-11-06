import Mathlib

open Real

theorem inequalities_599396 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (1 / 2) * (a + b) ^ 2 + (1 / 4) * (a + b) ≥ a * sqrt b + b * sqrt a := by
  have h1 : 0 < a := ha
  have h2 : 0 < b := hb
  have h3 : 0 < sqrt a := by 
    apply Real.sqrt_pos.mpr
    exact ha
  have h4 : 0 < sqrt b := by
    apply Real.sqrt_pos.mpr
    exact hb
  have h5 : sqrt a ^ 2 = a := Real.sq_sqrt (by linarith)
  have h6 : sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have h7 : 0 < sqrt a * sqrt b := mul_pos h3 h4
  have h8 : a * sqrt b + b * sqrt a ≤ (1 / 2) * (a + b) ^ 2 + (1 / 4) * (a + b) := by 
    nlinarith [sq_nonneg (sqrt a - sqrt b), sq_nonneg (sqrt a - 1 / 2), sq_nonneg (sqrt b - 1 / 2), 
            Real.sqrt_nonneg a, Real.sqrt_nonneg b, 
            Real.sq_sqrt (show 0 ≤ (a : ℝ) by linarith), 
            Real.sq_sqrt (show 0 ≤ (b : ℝ) by linarith), 
            mul_pos ha hb, 
            mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), sq_nonneg (sqrt a ^ 2 - a), sq_nonneg (sqrt b ^ 2 - b), 
            sq_nonneg (sqrt a - (sqrt b / 2)), sq_nonneg (sqrt b - (sqrt a / 2)), 
            sq_nonneg (a - b), 
            sq_nonneg (sqrt a * sqrt b - (a * b) / 4), 
            mul_pos (show 0 < sqrt a by assumption) (show 0 < sqrt b by assumption)
          ]
  linarith
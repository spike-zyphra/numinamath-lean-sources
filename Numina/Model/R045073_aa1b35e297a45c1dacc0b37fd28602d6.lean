import Mathlib

theorem inequalities_108107 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b) ≤ a + b := by
  have h1 : 0 ≤ Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  have h3 : (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b)) ^ 2 ≤ (a + b) ^ 2 := by
    nlinarith [sq_nonneg (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) - Real.sqrt (a * b)), 
      sq_nonneg (a - b), 
      Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + a * b + b ^ 2) / 3 by positivity), 
      Real.sq_sqrt (show (0 : ℝ) ≤ a * b by positivity), 
      mul_pos ha hb, 
      sq_nonneg (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b) - (a + b)), 
      mul_nonneg (Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3)) (Real.sqrt_nonneg (a * b)), 
      Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3), 
      Real.sqrt_nonneg (a * b), 
      sq_nonneg (Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) - ( (a + b) / 2 - Real.sqrt (a * b) )), 
      sq_nonneg (Real.sqrt (a * b) - ( (a + b) / 2 - Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) ))
    ]
  have h4 : Real.sqrt ((a ^ 2 + a * b + b ^ 2) / 3) + Real.sqrt (a * b) ≤ a + b := by
    nlinarith [h3, Real.sqrt_nonneg ((a ^ 2 + a * b + b ^ 2) / 3), Real.sqrt_nonneg (a * b), mul_pos ha hb]
  exact h4
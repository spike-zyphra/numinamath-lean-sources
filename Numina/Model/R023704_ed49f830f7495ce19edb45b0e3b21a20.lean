import Mathlib

open Real

theorem inequalities_55365 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    108 * (a * b + b * c + c * a) ≤
    (sqrt (a + b) + sqrt (b + c) + sqrt (c + a))^4 := by 
  have hab1 : 0 ≤ a + b := by linarith
  have hbc1 : 0 ≤ b + c := by linarith
  have hca1 : 0 ≤ c + a := by linarith
  have h1 : sqrt (a + b) ≥ 0 := by positivity
  have h2 : sqrt (b + c) ≥ 0 := by positivity
  have h3 : sqrt (c + a) ≥ 0 := by positivity
  nlinarith [sq_nonneg (sqrt (a + b) - sqrt (b + c)), sq_nonneg (sqrt (b + c) - sqrt (c + a)), sq_nonneg (sqrt (c + a) - sqrt (a + b)), 
          sq_nonneg (sqrt (a + b)^2 - sqrt (b + c)^2), sq_nonneg (sqrt (b + c)^2 - sqrt (c + a)^2), sq_nonneg (sqrt (c + a)^2 - sqrt (a + b)^2), 
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
          Real.sqrt_nonneg (a + b), Real.sqrt_nonneg (b + c), Real.sqrt_nonneg (c + a), 
          sq_nonneg (sqrt (a + b) + sqrt (b + c) - sqrt (c + a)), 
          sq_nonneg (sqrt (b + c) + sqrt (c + a) - sqrt (a + b)), 
          sq_nonneg (sqrt (a + b) + sqrt (c + a) - sqrt (b + c)), 
          Real.sq_sqrt (show 0 ≤ (a + b : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (b + c : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (c + a : ℝ) by linarith),
          mul_nonneg (Real.sqrt_nonneg (a + b)) (Real.sqrt_nonneg (b + c)), 
          mul_nonneg (Real.sqrt_nonneg (b + c)) (Real.sqrt_nonneg (c + a)), 
          mul_nonneg (Real.sqrt_nonneg (c + a)) (Real.sqrt_nonneg (a + b))
]
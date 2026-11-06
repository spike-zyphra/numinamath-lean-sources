import Mathlib

open Real

theorem inequalities_599653 (f : ℝ → ℝ) (hf : ∀ x, f x = sqrt (4 + x ^ 2)) (a b : ℝ) (ha : a ≠ b) :
    abs (f a - f b) < abs (a - b) := by
  have h1 : f a = sqrt (4 + a ^ 2) := hf a
  have h2 : f b = sqrt (4 + b ^ 2) := hf b
  rw [h1, h2]

  have h5 : (sqrt (4 + a ^ 2) - sqrt (4 + b ^ 2)) ^ 2 < (a - b) ^ 2 := by
    have h7 : sqrt (4 + a ^ 2) ^ 2 = 4 + a ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    have h8 : sqrt (4 + b ^ 2) ^ 2 = 4 + b ^ 2 := by
      rw [Real.sq_sqrt]
      positivity
    nlinarith [sq_nonneg (sqrt (4 + a ^ 2) - sqrt (4 + b ^ 2)), sq_nonneg (a - b), 
      sq_pos_of_ne_zero (show (a - b) ≠ 0 by intro h; apply ha; linarith), 
      sq_nonneg (sqrt (4 + a ^ 2) ^ 2 - sqrt (4 + b ^ 2) ^ 2), 
      mul_nonneg (Real.sqrt_nonneg (4 + a ^ 2)) (Real.sqrt_nonneg (4 + b ^ 2)), 
      sq_nonneg (a + b), sq_nonneg (a * b), 
      sq_nonneg (sqrt (4 + a ^ 2) * sqrt (4 + b ^ 2) - (4 + a * b)), 
      Real.sqrt_nonneg (4 + a ^ 2), Real.sqrt_nonneg (4 + b ^ 2), 
      Real.sq_sqrt (show 0 ≤ (4 + a ^ 2 : ℝ) by positivity), 
      Real.sq_sqrt (show 0 ≤ (4 + b ^ 2 : ℝ) by positivity), 
      sq_nonneg (a - b), sq_nonneg (sqrt (4 + a ^ 2) - sqrt (4 + b ^ 2))]
  
  have h6 : abs (sqrt (4 + a ^ 2) - sqrt (4 + b ^ 2)) < abs (a - b) := by
    apply sq_lt_sq.1 
    linarith [h5]
  
  exact h6
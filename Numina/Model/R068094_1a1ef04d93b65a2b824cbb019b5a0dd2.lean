import Mathlib

theorem algebra_287340 {A B x : ℝ} (hA : A + B = 5000) (hB : x > 0)
    (hA' : A * (1 + x / 100) = 2100) (hB' : B * (1 + (x + 1) / 100) = 3180) :
    A = 2000 ∧ B = 3000 := by
  
  have hB1 : B = 5000 - A := by linarith
  rw [hB1] at hB'
  
  have h1 : A = 2000 := by
    nlinarith [sq_nonneg (x - 10), sq_nonneg (A - 2000), sq_nonneg ((5000 - A) - 3000), 
        sq_nonneg (x), 
        sq_nonneg (A * (x - 0)), 
        sq_nonneg ((5000 - A) * (x + 1 - 0)), 
        mul_pos hB (show 0 < (10 : ℝ) by norm_num)]
  
  have h4 : B = 3000 := by
    linarith [hA, h1]
  
  constructor
  · exact h1
  · exact h4
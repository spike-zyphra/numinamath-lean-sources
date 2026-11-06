import Mathlib

open Real

theorem inequalities_190222 (x : ℝ) (hx : 2 < x ∧ x < 3) :
    logb 1.2 (x - 2) + logb 1.2 (x + 2) < logb 1.2 5 := by

  have hx1 : 2 < x := hx.1
  have hx2 : x < 3 := hx.2
  
  have h1 : x - 2 > 0 := by linarith
  have h2 : x + 2 > 0 := by linarith
  
  have h3 : logb 1.2 (x - 2) + logb 1.2 (x + 2) = logb 1.2 ((x - 2) * (x + 2)) := by 
    rw [← logb_mul (by linarith) (by linarith)]
  
  have h4 : (x - 2) * (x + 2) < 5 := by 
    nlinarith
  
  have h5 : (x - 2) * (x + 2) > 0 := by 
    nlinarith
  
  have h6 : logb 1.2 ((x - 2) * (x + 2)) < logb 1.2 5 := by
    apply logb_lt_logb
    all_goals
      nlinarith
  
  linarith [h3, h6]
import Mathlib
open Real

theorem algebra_11330 (a b c : ℝ) (ha : 1 < a) (hb : 1 < b) (hc : 1 < c)
(h1 : logb 10 a + logb b c = 3) (h2 : logb 10 b + logb a c = 4) :
logb 10 a * logb 10 c ≤ 16 / 3 := by

  have hbl1 : 0 < b := by linarith
  have hbl2 : b ≠ 1 := by linarith
  have hal1 : 0 < a := by linarith
  have hal2 : a ≠ 1 := by linarith
  have hcl1 : 0 < c := by linarith
  have hcl2 : c ≠ 1 := by linarith
  
  have eq1 : logb b c = logb 10 c / logb 10 b := by 
    field_simp [logb]
  
  have eq2 : logb a c = logb 10 c / logb 10 a := by 
    field_simp [logb]

  rw [eq1] at h1
  rw [eq2] at h2
  
  have pos1 : 0 < logb 10 b := by 
    apply logb_pos
    all_goals linarith
  
  have pos2 : 0 < logb 10 a := by 
    apply logb_pos
    all_goals linarith
  
  have eq3 : logb 10 a * logb 10 b + logb 10 c = 3 * logb 10 b := by
    have h4 : logb 10 b ≠ 0 := by 
      positivity
    field_simp [h4] at h1 ⊢
    nlinarith
  
  have eq4 : logb 10 b * logb 10 a + logb 10 c = 4 * logb 10 a := by
    have h5 : logb 10 a ≠ 0 := by 
      positivity
    field_simp [h5] at h2 ⊢
    nlinarith
  
  have eq5 : 3 * logb 10 b = 4 * logb 10 a := by
    nlinarith
  
  have eq6 : logb 10 c = 4 * logb 10 a - 4 / 3 * (logb 10 a)^2 := by 
    have eq7 : logb 10 b = 4 / 3 * logb 10 a := by
      nlinarith
    have eq8 : logb 10 c = 3 * logb 10 b - logb 10 a * logb 10 b := by 
      nlinarith [eq3]
    rw [eq7] at eq8
    rw [eq8]
    all_goals nlinarith
  
  have h3 : logb 10 a * logb 10 c ≤ 16 / 3 := by 
    rw [eq6]
    nlinarith [sq_nonneg (logb 10 a - 2), sq_nonneg (logb 10 a), sq_nonneg (logb 10 a - 4 / 3 * logb 10 a)]
  
  linarith [h3]
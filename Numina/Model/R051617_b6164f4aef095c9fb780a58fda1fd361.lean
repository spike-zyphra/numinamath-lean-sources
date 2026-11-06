import Mathlib

theorem algebra_3656 {a b : ℝ} (ha : a^2 = 2017*a - 10000) (hb : b^2 = 2017*b - 10000) (hab : a > b) : (a - b)^2 = 4028289 := by 
  have h : a + b = 2017 := by 
    have h1 : a^2 - b^2 = 2017 * (a - b) := by 
      linarith [ha, hb]
    have h2 : a^2 - b^2 = (a + b) * (a - b) := by 
      ring
    rw [h2] at h1
    have h3 : a - b ≠ 0 := by linarith
    have h4 : a + b = 2017 := by 
      apply (mul_left_inj' h3).mp
      linarith
    exact h4
  
  have hab2 : a * b = 10000 := by 
    nlinarith [ha, hb, h]
  
  have h1 : (a - b) ^ 2 = (a + b) ^ 2 - 4 * (a * b) := by 
    ring
  
  rw [h1, h, hab2]
  norm_num
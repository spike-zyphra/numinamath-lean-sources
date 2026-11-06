import Mathlib

theorem algebra_8157 {a m : ℝ} (ha : |a + 4| = -(m - 3)^2) : a^m = -64 := by
  have h1 : |a + 4| ≥ 0 := abs_nonneg (a + 4)
  have h2 : -(m - 3)^2 ≤ 0 := by 
    have h5 : (m - 3)^2 ≥ 0 := sq_nonneg (m - 3)
    linarith
  
  have h3 : |a + 4| = 0 := by
    linarith [abs_nonneg (a + 4), sq_nonneg (m - 3)]
  
  have h4 : (m - 3)^2 = 0 := by 
    linarith [abs_nonneg (a + 4), sq_nonneg (m - 3)]
    
  have ha' : a + 4 = 0 := abs_eq_zero.mp h3
  have hm' : m - 3 = 0 := pow_eq_zero h4
  
  have ha'' : a = -4 := by linarith
  have hm'' : m = 3 := by linarith
  
  rw [ha'', hm'']
  norm_num
import Mathlib

theorem algebra_19399 (a b : ℝ) (ha : a * 4 = -1) (hb : 2 * a + b = 1) :
    6 * a + b = 0 := by 
  have ha' : a = -1/4 := by 
    linarith
  have hb' : b = 3/2 := by 
    rw [ha'] at hb 
    linarith 
  rw [ha', hb']
  norm_num
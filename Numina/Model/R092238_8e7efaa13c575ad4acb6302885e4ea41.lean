import Mathlib

theorem algebra_276837 {a b : ℝ} (ha : 1 < a) (hb : 1 < b) (h : Real.log (a + b) = Real.log a + Real.log b) :
    Real.log (a - 1) + Real.log (b - 1) = 0 := by

  have h1 : a + b > 0 := by linarith
  have h2 : a > 0 := by linarith
  have h3 : b > 0 := by linarith

  have h4 : Real.log (a * b) = Real.log a + Real.log b := by
    rw [Real.log_mul (by linarith) (by linarith)]
    
  have h5 : Real.log (a + b) = Real.log (a * b) := by
    linarith [h, h4]

  have h7 : a + b = a * b := by 
    have h8 : a + b > 0 := by linarith
    have h9 : a * b > 0 := mul_pos (show 0 < a by linarith) (show 0 < b by linarith)
    have h10 : Real.log (a + b) = Real.log (a * b) := by 
      linarith [h5]
    have h11 : a + b > 0 := by nlinarith
    have h12 : a * b > 0 := mul_pos (show 0 < a by linarith) (show 0 < b by linarith)
    have h13 : a + b = a * b := by 
      apply Real.log_injOn_pos (Set.mem_Ioi.mpr h11) (Set.mem_Ioi.mpr h12) h10
    linarith

  have h5 : Real.log (a - 1) + Real.log (b - 1) = Real.log ((a - 1) * (b - 1)) := by 
    have ha1 : a - 1 > 0 := by linarith
    have hb1 : b - 1 > 0 := by linarith
    rw [← Real.log_mul (by linarith) (by linarith)]
   
  have h6 : (a - 1) * (b - 1) = 1 := by 
    nlinarith [h7]

  rw [h5]
  rw [h6]
  norm_num
  all_goals linarith
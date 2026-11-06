import Mathlib

theorem algebra_9938 {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (h : Real.log (a + b) = Real.log a + Real.log b) :
    Real.log (a - 1) + Real.log (b - 1) = 0 := by

  have h1 : a + b > 0 := by linarith
  have h2 : a > 0 := by linarith
  have h3 : b > 0 := by linarith

  have h4 : Real.log (a + b) = Real.log (a * b) := by
    have h5 : Real.log a + Real.log b = Real.log (a * b) := by 
      rw [Real.log_mul (by linarith) (by linarith)]
    linarith [h, h5]
  
  have h6 : a + b = a * b := by
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr (show 0 < a * b by positivity)) h4
  
  have h7 : (a - 1) * (b - 1) = 1 := by
    nlinarith
  
  have h8 : a - 1 > 0 := by linarith
  have h9 : b - 1 > 0 := by linarith
  
  have h10 : Real.log (a - 1) + Real.log (b - 1) = Real.log ((a - 1) * (b - 1)) := by
    rw [← Real.log_mul (by linarith) (by linarith)]
  
  rw [h10]
  rw [h7]
  simp
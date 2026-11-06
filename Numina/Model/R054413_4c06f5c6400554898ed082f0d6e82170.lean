import Mathlib

open Real

theorem algebra_286469 {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (h : log (a + b) = log a + log b) :
    log (a - 1) + log (b - 1) = 0 := by
  have h1 : a + b > 0 := by nlinarith
  have h2 : a > 0 := by nlinarith
  have h3 : b > 0 := by nlinarith
  
  have h4 : log (a + b) = log (a * b) := by 
    rw [h]
    have h5 : log a + log b = log (a * b) := by
      rw [log_mul (by nlinarith) (by nlinarith)]
    linarith [h5]
  
  have h6 : a + b = a * b := by
    have h7 : a + b > 0 := by nlinarith
    have h8 : a * b > 0 := by nlinarith
    have h9 : log (a + b) = log (a * b) := h4
    have h10 : (a + b) = (a * b) := by
      exact log_injOn_pos (Set.mem_Ioi.mpr h7) (Set.mem_Ioi.mpr h8) h9
    exact h10
  
  have h11 : (a - 1) * (b - 1) = 1 := by 
    nlinarith [h6]
  
  have h12 : log (a - 1) + log (b - 1) = log ((a - 1) * (b - 1)) := by
    rw [log_mul (by nlinarith) (by nlinarith)]
  
  rw [h12]
  rw [h11]
  norm_num
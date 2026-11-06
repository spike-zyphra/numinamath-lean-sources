import Mathlib

theorem algebra_153586 (x : ℝ) (hx : x > 7) :
    Real.logb 3 (12 * x + 4) - Real.logb 3 (x - 7) ≠ Real.logb 3 9 := by 
  intro h 
  have h1 : Real.logb 3 (12 * x + 4) - Real.logb 3 (x - 7) = Real.logb 3 ((12 * x + 4) / (x - 7)) := by
    rw [← Real.logb_div (by linarith) (by linarith)]
  rw [h1] at h 
  have h2 : (12 * x + 4) / (x - 7) = (9 : ℝ) := by 
    have h3 : Real.logb 3 ((12 * x + 4) / (x - 7)) = Real.logb 3 9 := h 
    have h4 : (12 * x + 4) / (x - 7) > 0 := by 
      apply div_pos 
      linarith 
      linarith 
    have h5 : (9 : ℝ) > 0 := by norm_num 
    have h6 : (12 * x + 4) / (x - 7) = (9 : ℝ) := by 
      apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h4) (Set.mem_Ioi.mpr h5) h3 
    linarith 
  have h7 : (12 * x + 4) / (x - 7) = (9 : ℝ) := h2 
  have h8 : x - 7 > 0 := by linarith 
  have h9 : 12 * x + 4 = 9 * (x - 7) := by 
    have h10 : (12 * x + 4) / (x - 7) = (9 : ℝ) := h7 
    field_simp [show x - 7 ≠ 0 by linarith] at h10 ⊢ 
    nlinarith 
  nlinarith
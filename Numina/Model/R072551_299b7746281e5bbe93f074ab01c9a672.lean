import Mathlib

open Real

theorem algebra_269856 {a b : ℝ} (ha : 1 < a) (hb : 1 < b)
    (p : ℝ) (hp : p = logb b (logb b a) / logb b a) :
    a ^ p = logb b a := by 
  have h1 : 0 < a := by linarith
  have h2 : 0 < b := by linarith
  have h5 : logb b a ≠ 0 := by
    have h6 : logb b a > 0 := by
      apply logb_pos
      all_goals linarith
    linarith

  rw [hp]
  have h7 : logb b (logb b a) = (log (logb b a)) / (log b) := by 
    field_simp [logb]
  
  have h8 : (log b) ≠ 0 := by 
    apply ne_of_gt
    apply log_pos 
    linarith
  
  have h9 : logb b a = (log a) / (log b) := by 
    field_simp [logb]
  
  have h10 : log a > 0 := by 
    apply log_pos 
    linarith
  
  have h11 : log b > 0 := by 
    apply log_pos 
    linarith
  
  rw [h7]

  have h_eq : (a : ℝ) ^ ((log (logb b a) / log b) / logb b a) = logb b a := by
    have h12 : (a : ℝ) ^ ((log (logb b a) / log b) / logb b a) = 
              exp ((log a) * ((log (logb b a) / log b) / logb b a)) := by 
      rw [Real.rpow_def_of_pos h1]
      all_goals linarith
    have h13 : (log a) * ((log (logb b a) / log b) / logb b a) = (log (logb b a)) := by
      have h14 : logb b a = (log a) / (log b) := by 
        field_simp [logb]
      rw [h14]
      field_simp [h10, h11]
      <;> ring_nf <;> simp [h10, h11] <;> ring
    rw [h12]
    rw [h13]
    have h15 : logb b a > 0 := by
      apply logb_pos
      all_goals linarith
    have h16 : exp (log (logb b a)) = (logb b a) := by
      rw [exp_log]
      all_goals linarith
    rw [h16]
  
  exact h_eq
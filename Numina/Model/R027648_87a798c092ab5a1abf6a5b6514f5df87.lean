import Mathlib

theorem algebra_207953 {a b x : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b ∧ b ≠ 1) (hx : 0 < x)
    (h1 : Real.logb a x = 3) (h2 : Real.logb (a * b) x = 2) :
    Real.logb b x = 6 := by
  have ha1 : a > 0 := ha.1
  have ha2 : a ≠ 1 := ha.2
  have hb1 : b > 0 := hb.1
  have hb2 : b ≠ 1 := hb.2
  have hx_pos : x > 0 := hx
  
  have h1' : Real.logb a x = (Real.log x) / (Real.log a) := by 
    field_simp [Real.logb]
    all_goals linarith
  
  have h2' : Real.logb (a * b) x = (Real.log x) / (Real.log (a * b)) := by 
    field_simp [Real.logb]
    all_goals linarith
  
  rw [h1'] at h1
  rw [h2'] at h2
  
  have h4 : Real.log a ≠ 0 := by
    have ha1' : a > 0 := ha1
    have ha2' : a ≠ 1 := ha2
    exact Real.log_ne_zero_of_pos_of_ne_one ha1' ha2'
  
  have h5 : Real.log b ≠ 0 := by
    have hb1' : b > 0 := hb1
    have hb2' : b ≠ 1 := hb2
    exact Real.log_ne_zero_of_pos_of_ne_one hb1' hb2'
  
  have eq1 : Real.log x = 3 * Real.log a := by
    have h4' : Real.log a ≠ 0 := h4
    field_simp [h4'] at h1 ⊢
    linarith
  
  have h7 : Real.log a = 2 * Real.log b := by 
    have eq2 : Real.log x = 2 * (Real.log a + Real.log b) := by 
      have h6' : Real.log (a * b) = Real.log a + Real.log b := by 
        rw [Real.log_mul (by linarith) (by linarith)]
      have h2_rw : Real.log x / (Real.log (a * b)) = 2 := by 
        simpa using h2
      rw [h6'] at h2_rw
      have h7_ne_zero : Real.log a + Real.log b ≠ 0 := by 
        by_contra h
        have : Real.log a + Real.log b = 0 := by linarith
        have h8 : Real.log x / (Real.log a + Real.log b) = 2 := by 
          simpa using h2_rw
        rw [show Real.log a + Real.log b = (0 : ℝ) by linarith] at h8
        norm_num at h8 ⊢ 
        all_goals try linarith
        all_goals try tauto
        all_goals try nlinarith
        all_goals try tauto
      field_simp [h7_ne_zero] at h2_rw ⊢
      <;> nlinarith 
      all_goals try linarith
      all_goals try nlinarith 
      all_goals try tauto
      all_goals try nlinarith
      all_goals try linarith
      all_goals try tauto
    nlinarith [eq1, eq2]
  
  have h8 : Real.log x = 6 * Real.log b := by 
    nlinarith [eq1, h7]
  
  have h6' : Real.logb b x = (Real.log x) / (Real.log b) := by 
    field_simp [Real.logb]
    all_goals try linarith
  
  rw [h6']
  have h9 : Real.log b ≠ 0 := h5
  have h10 : Real.log x = 6 * Real.log b := h8
  rw [show Real.log x = 6 * Real.log b by linarith [h10]]
  field_simp [h9]
  <;> nlinarith [h9, h10]
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
  all_goals try tauto
  all_goals try nlinarith
  all_goals try linarith
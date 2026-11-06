import Mathlib

theorem algebra_11391 {a b c : ℝ} (ha : a = Real.logb 8 5) (hb : b = Real.logb 4 3) (hc : c = 2 / 3) :
    b > a ∧ a > c := by
  have ha' : a = Real.log 5 / Real.log 8 := by 
    rw [ha]
    field_simp [Real.logb]
  
  have hb' : b = Real.log 3 / Real.log 4 := by 
    rw [hb]
    field_simp [Real.logb]

  have h1 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
    simp [Real.log_pow]
    all_goals linarith
  
  have ha'' : a = Real.log 5 / (3 * Real.log 2) := by
    rw [ha']
    rw [h1]
  
  have hb'' : b = Real.log 3 / (2 * Real.log 2) := by
    rw [hb']
    rw [h2]

  have h3 : Real.log 2 > 0 := by
    apply Real.log_pos
    all_goals linarith
  
  have h3' : b > a := by
    rw [hb'', ha'']
    have h4 : 3 * Real.log 3 > 2 * Real.log 5 := by 
      have h5 : 3 * Real.log 3 = Real.log (3 ^ 3 : ℝ) := by
        simp [Real.log_pow]
      have h6 : 2 * Real.log 5 = Real.log (5 ^ 2 : ℝ) := by 
        simp [Real.log_pow]
      rw [h5, h6]
      have h7 : Real.log (3 ^ 3 : ℝ) > Real.log (5 ^ 2 : ℝ) := by
        apply Real.log_lt_log
        all_goals norm_num
      linarith
    have h5 : Real.log 3 / (2 * Real.log 2) > Real.log 5 / (3 * Real.log 2) := by 
      have h6 : Real.log 2 > 0 := h3
      have h7 : 3 * Real.log 3 > 2 * Real.log 5 := h4
      have h8 : Real.log 3 / (2 * Real.log 2) - Real.log 5 / (3 * Real.log 2) > 0 := by
        have pos1 : 2 * Real.log 2 > 0 := by nlinarith
        have pos2 : 3 * Real.log 2 > 0 := by nlinarith
        have h9 : Real.log 3 / (2 * Real.log 2) - Real.log 5 / (3 * Real.log 2) =
            (3 * Real.log 3 - 2 * Real.log 5) / (6 * Real.log 2) := by 
          field_simp
          <;> ring
        rw [h9]
        apply div_pos
        linarith
        all_goals linarith
      linarith
    linarith

  have h4 : a > c := by
    rw [ha'', hc]
    have h3 : Real.log 2 > 0 := h3
    have h4 : Real.log 5 > 2 * Real.log 2 := by 
      have h5 : Real.log 5 > Real.log (4 : ℝ) := by 
        apply Real.log_lt_log
        all_goals norm_num
      have h6 : Real.log (4 : ℝ) = 2 * Real.log 2 := by 
        rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num]
        simp [Real.log_pow]
      linarith
    have h5 : Real.log 5 / (3 * Real.log 2) > (2 / 3 : ℝ) := by
      have pos1 : Real.log 2 > 0 := h3
      have h6 : Real.log 5 > 2 * Real.log 2 := h4
      have h7 : Real.log 5 / (3 * Real.log 2) - (2 / 3 : ℝ) > 0 := by
        have h8 : Real.log 2 > 0 := h3
        have h9 : Real.log 5 / (3 * Real.log 2) - (2 / 3 : ℝ) = (Real.log 5 - 2 * Real.log 2) / (3 * Real.log 2) := by 
          field_simp
          <;> ring
        rw [h9]
        apply div_pos
        linarith
        all_goals linarith
      linarith
    linarith
  
  constructor
  · linarith [h3']
  · linarith [h4]
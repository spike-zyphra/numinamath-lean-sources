import Mathlib

theorem algebra_179763 {a b : ℝ} (ha : 0 < a ∧ a ≠ 1) (hb : 0 < b) (h : Real.logb a 27 = b) :
    Real.logb (Real.sqrt 3) (a ^ ((1 : ℝ) / 6)) = 1 / b := by 
  have h1 : Real.logb a 27 = b := h 
  have ha1 : 0 < a := ha.1 
  have ha2 : a ≠ 1 := ha.2 
  have h5 : Real.logb a 27 = Real.log 27 / Real.log a := by 
    field_simp [Real.logb]
    all_goals linarith
  rw [h5] at h1 
  have h6 : Real.log 27 = 3 * Real.log 3 := by 
    calc 
      Real.log 27 = Real.log (3 ^ 3) := by norm_num 
      _ = 3 * Real.log 3 := by simp [Real.log_pow]
  rw [h6] at h1 
  have h7 : Real.log a ≠ 0 := by 
    by_contra h'
    have h8 : 3 * Real.log 3 / Real.log a = 0 := by 
      field_simp [h']
      all_goals linarith 
    have h9 : 3 * Real.log 3 / Real.log a = b := by 
      linarith 
    have h10 : b = 0 := by 
      linarith [h8, h9] 
    linarith [hb.ne']
  have h7' : Real.log 3 > 0 := by 
    have h8 : Real.log 3 > 0 := by 
      apply Real.log_pos 
      all_goals norm_num 
    linarith 
  have h4 : Real.log a = 3 * Real.log 3 / b := by 
    have h9 : 3 * Real.log 3 / Real.log a = b := by 
      field_simp [(show Real.log a ≠ 0 by exact h7)] at h1 ⊢ 
      <;> linarith 
    have h12 : Real.log a ≠ 0 := h7 
    have h13 : Real.log a = 3 * Real.log 3 / b := by 
      have h14 : 3 * Real.log 3 / Real.log a = b := by 
        linarith 
      have h15 : Real.log a = 3 * Real.log 3 / b := by 
        have h16 : (3 * Real.log 3 / Real.log a) = b := by linarith 
        have h17 : Real.log a ≠ 0 := h7 
        field_simp [(show Real.log a ≠ 0 by exact h7)] at h16 ⊢ 
        <;> nlinarith [Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
      linarith 
    linarith 
  have h5' : Real.logb (Real.sqrt 3) (a ^ ((1 : ℝ) / 6)) = Real.log (a ^ ((1 : ℝ) / 6)) / Real.log (Real.sqrt 3) := by 
    field_simp [Real.logb]
  rw [h5']
  have h8 : Real.log (a ^ ((1 : ℝ) / 6)) = (1 / 6) * Real.log a := by 
    rw [Real.log_rpow]
    all_goals linarith 
  have h9 : Real.log (Real.sqrt 3) = (1 / 2) * Real.log 3 := by 
    have h10 : Real.sqrt 3 = (3 : ℝ) ^ ((1 : ℝ) / 2) := by 
      rw [Real.sqrt_eq_rpow]
    have h11 : Real.log ((3 : ℝ) ^ ((1 : ℝ) / 2)) = (1 / 2) * Real.log 3 := by 
      rw [Real.log_rpow]
      all_goals norm_num 
    rw [h10]
    linarith 
  rw [h8, h9, h4] 
  have h14 : b ≠ 0 := by 
    linarith [hb.ne']
  have h15 : Real.log 3 > 0 := h7' 
  field_simp [(show b ≠ 0 by exact h14), (show Real.log 3 > 0 by linarith [h15])]
  <;> ring_nf <;> linarith [Real.log_pos (show (3 : ℝ) > 1 by norm_num)]
  all_goals linarith
import Mathlib

open Real

theorem algebra_261 {a b : ℝ} (hab : a + b = 2) (h : (1 - a)^2 / b + (1 - b)^2 / a = -4) :
    a * b = -1 := by

  have ha1 : a ≠ 0 := by
    by_contra h1
    have ha1' : a = 0 := by linarith
    rw [ha1'] at hab h
    have hb : b = 2 := by linarith
    rw [hb] at h
    norm_num [ha1'] at h
    all_goals linarith
  have hb1 : b ≠ 0 := by
    by_contra h1
    have hb1' : b = 0 := by linarith
    rw [hb1'] at hab h
    have ha : a = 2 := by linarith
    rw [ha] at h
    norm_num [hb1'] at h
    all_goals linarith
  
  have eq1 : (1 - a) ^ 2 * a + (1 - b) ^ 2 * b = -4 * (a * b) := by
    have eq5' : ( (1 - a)^2 * a + (1 - b)^2 * b ) / (a * b) = -4 := by 
      have eq6' : (1 - a) ^ 2 / b + (1 - b) ^ 2 / a = ( (1 - a)^2 * a + (1 - b) ^ 2 * b ) / (a * b) := by 
        have eq7' : (1 - a) ^ 2 / b = (1 - a) ^ 2 * a / (a * b) := by 
          field_simp [hb1, ha1]
          <;> ring 
        have eq8' : (1 - b) ^ 2 / a = (1 - b) ^ 2 * b / (a * b) := by 
          field_simp [hb1, ha1]
          <;> ring 
        have eq9' : (1 - a) ^ 2 / b + (1 - b) ^ 2 / a = ( (1 - a) ^ 2 * a + (1 - b) ^ 2 * b ) / (a * b) := by 
          rw [eq7', eq8']
          <;> ring 
        linarith 
      linarith [eq6', h]
    have h1 : a * b ≠ 0 := by 
      apply mul_ne_zero 
      exact ha1 
      exact hb1 
    have eq6 : (1 - a) ^ 2 * a + (1 - b) ^ 2 * b = -4 * (a * b) := by 
      have eq7 : ( (1 - a) ^ 2 * a + (1 - b) ^ 2 * b ) / (a * b) = -4 := eq5'
      field_simp [h1] at eq7 ⊢ 
      <;> nlinarith 
    linarith [eq6]

  have eq2 : a^3 + b^3 + a + b - 2 * a^2 - 2 * b^2 + 4 * (a * b) = 0 := by 
    nlinarith [eq1]
  have eq3 : a^3 + b^3 = (a + b) ^ 3 - 3 * (a * b) * (a + b) := by
    ring 
  rw [eq3] at eq2
  rw [show a + b = 2 by linarith] at eq2 
  -- Now solve for a * b 
  have eq4 : a^2 + b^2 = (a + b) ^ 2 - 2 * (a * b) := by 
    ring 
  rw [show a + b = 2 by linarith] at eq4 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_pos_of_pos (show (1 : ℝ) > 0 by norm_num)]
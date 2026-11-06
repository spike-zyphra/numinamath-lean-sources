import Mathlib

theorem algebra_298880 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h : ∃ x, 2 + Real.logb 2 a = x ∧ 3 + Real.logb 3 b = x ∧ Real.logb 6 (a + b) = x) :
    1 / a + 1 / b = 108 := by 
  rcases h with ⟨x, h₁, h₂, h₃⟩ 
  have ha2 : a = (2 : ℝ) ^ (x - 2) := by 
    have h1 : Real.logb 2 a = x - 2 := by linarith
    have h2 : a = (2 : ℝ) ^ (Real.logb 2 a) := by 
      field_simp at *
    rw [h1] at h2
    linarith 
  have hb2 : b = (3 : ℝ) ^ (x - 3) := by 
    have h1 : Real.logb 3 b = x - 3 := by linarith 
    have h2 : b = (3 : ℝ) ^ (Real.logb 3 b) := by 
      field_simp at *
    rw [h1] at h2 
    linarith 
  have h_eq3 : a + b = (6 : ℝ) ^ x := by 
    have h3 : Real.logb 6 (a + b) = x := h₃ 
    have h4 : a + b > 0 := by nlinarith 
    have h5 : (a + b : ℝ) = (6 : ℝ) ^ (Real.logb 6 (a + b : ℝ)) := by 
      field_simp at *
    rw [h3] at h5 
    linarith 
  have h_eq4 : 1 / a + 1 / b = (a + b) / (a * b) := by 
    field_simp 
    <;> nlinarith 
  have hab : a * b = (6 : ℝ) ^ x / 108 := by 
    rw [ha2, hb2] 
    have h_eq5 : ((2 : ℝ) ^ (x - 2 : ℝ)) * ((3 : ℝ) ^ (x - 3 : ℝ)) = (2 : ℝ) ^ x * (3 : ℝ) ^ x / 108 := by 
      have h_eq6 : ((2 : ℝ) ^ (x - 2 : ℝ)) = (2 : ℝ) ^ x / (2 : ℝ) ^ (2 : ℝ) := by 
        rw [show x - 2 = x - (2 : ℝ) by ring] 
        rw [Real.rpow_sub] 
        all_goals linarith 
      have h_eq7 : ((3 : ℝ) ^ (x - 3 : ℝ)) = (3 : ℝ) ^ x / (3 : ℝ) ^ (3 : ℝ) := by 
        rw [show x - 3 = x - (3 : ℝ) by ring] 
        rw [Real.rpow_sub] 
        all_goals linarith 
      rw [h_eq6, h_eq7] 
      have h_eq8 : (2 : ℝ) ^ (2 : ℝ) = (4 : ℝ) := by norm_num 
      have h_eq9 : (3 : ℝ) ^ (3 : ℝ) = (27 : ℝ) := by norm_num 
      rw [h_eq8, h_eq9] 
      field_simp 
      <;> ring_nf 
    have h_eq6x : (2 : ℝ) ^ x * (3 : ℝ) ^ x = (6 : ℝ) ^ x := by 
      have h_eq7 : (6 : ℝ) ^ x = (2 * 3) ^ x := by norm_num 
      calc 
        (2 : ℝ) ^ x * (3 : ℝ) ^ x = (2 * 3) ^ x := by rw [Real.mul_rpow]; all_goals linarith 
        _ = (6 : ℝ) ^ x := by rw [h_eq7] 
    rw [h_eq6x] at h_eq5 
    linarith 
  rw [h_eq4] 
  rw [show (a + b) = (6 : ℝ) ^ x by linarith [h_eq3]] 
  rw [hab] 
  have hne : (6 : ℝ) ^ x ≠ 0 := by positivity 
  field_simp at *
  <;> nlinarith
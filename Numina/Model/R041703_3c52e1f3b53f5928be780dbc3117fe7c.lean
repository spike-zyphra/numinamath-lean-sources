import Mathlib

theorem algebra_253106 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) 
    (h₁ : a + b > c) (h₂ : a + c > b) (h₃ : b + c > a)
    (h : 1 / (a + c) + 1 / (b + c) = 3 / (a + b + c)) :
    Real.arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) = Real.pi / 3 := by
  have h4 : (a + c) * (b + c) * (a + b + c) > 0 := by
    have h4a : 0 < a + c := by linarith
    have h4b : 0 < b + c := by linarith
    have h4c : 0 < a + b + c := by linarith
    positivity
  have h5 : (b + c) * (a + b + c) + (a + c) * (a + b + c) = 3 * ((a + c) * (b + c)) := by 
    have h6 : a + c > 0 := by linarith
    have h7 : b + c > 0 := by linarith
    have h8 : a + b + c > 0 := by linarith
    field_simp [h6, h7, h8] at h 
    nlinarith [h, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
  have h6 : a ^ 2 + b ^ 2 - c ^ 2 = a * b := by
    nlinarith [h5, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc]
  have h7 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = 1 / 2 := by
    have h8 : 0 < 2 * a * b := by nlinarith
    have h9 : a ^ 2 + b ^ 2 - c ^ 2 = a * b := h6
    have h10 : a ^ 2 + b ^ 2 - c ^ 2 = a * b := h9
    have h11 : (a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b) = (a * b) / (2 * a * b) := by
      rw [h10]
    have h12 : (a * b) / (2 * a * b) = 1 / 2 := by 
      have h13 : 0 < 2 * a * b := h8 
      have h14 : a * b > 0 := mul_pos ha hb 
      field_simp [show 0 < a by linarith, show 0 < b by linarith] at *
      <;> nlinarith
    linarith [h11, h12]
  have h8 : Real.arccos ((a ^ 2 + b ^ 2 - c ^ 2) / (2 * a * b)) = Real.arccos (1 / 2) := by 
    rw [h7]
  have h9 : Real.arccos (1 / 2) = Real.pi / 3 := by 
    have h10 : Real.cos (Real.pi / 3) = 1 / 2 := Real.cos_pi_div_three
    have h11 : Real.arccos (Real.cos (Real.pi / 3)) = Real.pi / 3 := by
      apply Real.arccos_cos
      all_goals linarith [Real.pi_pos]
    rw [h10] at h11 
    linarith
  rw [h9] at h8 
  linarith [h8]
import Mathlib

theorem algebra_182201 {a b : ℝ} (h : b ≠ 0) (h1 : (a + b) / b = 1.4) : (b - a) / a = 3 / 2 := by
  have h2 : a + b = 1.4 * b := by 
    have h3 : b ≠ 0 := h
    field_simp [h3] at h1 
    linarith
  have h4 : a = 0.4 * b := by 
    nlinarith 
  have ha : a ≠ 0 := by 
    by_contra h6
    have h7 : a = 0 := by linarith 
    rw [h7] at h4 
    have h8 : 0.4 * b = 0 := by 
      linarith 
    have h9 : b = 0 := by 
      norm_num at h8 ⊢
      nlinarith 
    contradiction 
  have h5 : b = (5 / 2) * a := by 
    have h4' : a = (0.4 : ℝ) * b := h4 
    have h8 : (0.4 : ℝ) ≠ 0 := by 
      norm_num 
    have eq3 : b = (a) / (0.4 : ℝ) := by 
      field_simp [h8]
      nlinarith 
    rw [eq3] 
    field_simp [h8]
    <;> ring_nf <;> nlinarith 
  have eq4 : b - a = (3 / 2) * a := by 
    nlinarith [h5] 
  have eq5 : (b - a) / a = ((3 / 2) * a) / a := by 
    rw [eq4] 
  have eq6 : ((3 / 2) * a) / a = (3 / 2) := by 
    have ha' : a ≠ 0 := ha 
    field_simp [ha'] 
    <;> nlinarith 
  rw [eq5] 
  linarith [eq6]
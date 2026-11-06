import Mathlib

theorem other_307519 (v1 v2 : ℝ) (h : v1 > 0) (h' : v2 > 0)
    (h1 : 12 + 2 = 12 + v1 / v2) (h2 : 12 + 4 = 12 + v1 / v2 + 90 / v2) :
    ¬(12 + 2 = 12 + v1 / v2 + 60 / v2) := by
  have h_eq1 : v1 / v2 = 2 := by
    field_simp at h1 ⊢
    nlinarith
  have h3 : v1 = 2 * v2 := by 
    have h_eq1 : v1 / v2 = 2 := by
      field_simp at h1 ⊢
      nlinarith
    field_simp at h_eq1 ⊢
    nlinarith 
  rw [show v1 = 2 * v2 by linarith [h3]] at h2
  have h4 : v2 = 45 := by 
    field_simp at h2 ⊢ 
    nlinarith
  intro h'
  have h_eq2 : 60 / v2 = 4 / 3 := by
    rw [show v2 = 45 by linarith [h4]]
    norm_num
  have h_eq3 : v1 / v2 = 2 := by
    have h_eq1 : v1 / v2 = 2 := by
      field_simp at h1 ⊢
      nlinarith
    linarith [h_eq1]
  field_simp [h_eq3, h_eq2] at h' ⊢
  <;> nlinarith
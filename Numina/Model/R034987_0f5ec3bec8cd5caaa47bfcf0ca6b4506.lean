import Mathlib

  theorem algebra_132534 {a : ℝ} (ha : 2 * a - 1 / a = 3) :
  16 * a ^ 4 + 1 / a ^ 4 = 161 := by
  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at ha
    norm_num at ha
  have h_eq : 2 * a ^ 2 - 3 * a - 1 = 0 := by
    have h1 : a ≠ 0 := ha1
    have h2 : 2 * a - 1 / a = 3 := by linarith [ha]
    field_simp [h1] at h2
    linarith [h2]
  have h_eq2 : 4 * a ^ 2 + 1 / a ^ 2 = 13 := by
    have h1 : a ≠ 0 := ha1
    have h_eq1 : 2 * a - 1 / a = 3 := by linarith [ha]
    have h_eq2 : (2 * a - 1 / a) ^ 2 = 9 := by
      rw [h_eq1]
      norm_num
    have h_eq3 : (2 * a - 1 / a) ^ 2 = 4 * a^2 - 4 + 1 / a ^ 2 := by
      field_simp [h1]
      ring
    rw [h_eq3] at h_eq2
    have h_eq4 : 4 * a ^ 2 + 1 / a ^ 2 = 13 := by
      linarith 
    exact h_eq4
  have h_eq3 : 16 * a ^ 4 + 1 / a ^ 4 = 161 := by
    have h2 : 4 * a ^ 2 + 1 / a ^ 2 = 13 := h_eq2
    have h_eq4 : (4 * a ^ 2 + 1 / a ^ 2) ^ 2 = 169 := by
      rw [h2]
      norm_num
    have h_eq5 : (4 * a ^ 2 + 1 / a ^ 2) ^ 2 = 16 * a ^ 4 + 8 + 1 / a ^ 4 := by 
      have h1 : a ≠ 0 := ha1
      field_simp [h1]
      ring
    have h_eq6 : 16 * a ^ 4 + 1 / a ^ 4 = 161 := by 
      linarith [h_eq4, h_eq5]
    exact h_eq6
  exact h_eq3
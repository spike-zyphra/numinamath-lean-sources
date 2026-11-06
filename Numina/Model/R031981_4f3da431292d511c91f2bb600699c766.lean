import Mathlib

theorem algebra_321609 {a b c : ℝ} (h₀ : a * b / (a + b) = 1 / 3) (h₁ : b * c / (b + c) = 1 / 4)
    (h₂ : c * a / (c + a) = 1 / 5) : a * b + b * c + c * a = 1 := by

  have h3 : a + b ≠ 0 := by
    by_contra h
    have h4 : a * b / (a + b) = 0 := by
      rw [h]
      norm_num
    linarith
  have h4 : b + c ≠ 0 := by
    by_contra h
    have h5 : b * c / (b + c) = 0 := by
      rw [h]
      norm_num
    linarith
  have h5 : c + a ≠ 0 := by
    by_contra h
    have h6 : c * a / (c + a) = 0 := by
      rw [h]
      norm_num
    linarith

  have eq1 : 3 * a * b = a + b := by
    have h3' : a + b ≠ 0 := h3
    field_simp at h₀
    linarith
  have eq2 : 4 * b * c = b + c := by
    have h4' : b + c ≠ 0 := h4
    field_simp at h₁
    linarith
  have eq3 : 5 * c * a = c + a := by
    have h5' : c + a ≠ 0 := h5
    field_simp at h₂
    linarith

  have ha1 : a ≠ 0 := by
    by_contra h
    rw [h] at eq1
    have h0 : 3 * (0 : ℝ) * b = (0 : ℝ) + b := by
      linarith
    have h_b_zero : b = 0 := by
      linarith
    have h_zero : a + b = 0 := by
      linarith [h, h_b_zero]
    contradiction
  have hb1 : b ≠ 0 := by
    by_contra h
    rw [h] at eq1
    have h0 : 3 * a * (0 : ℝ) = a + (0 : ℝ) := by
      linarith
    have h_a_zero : a = 0 := by
      linarith
    have h_zero : a + b = 0 := by
      linarith [h_a_zero, h]
    contradiction
  have hc1 : c ≠ 0 := by
    by_contra h
    rw [h] at eq2
    have h0 : 4 * b * (0 : ℝ) = b + (0 : ℝ) := by
      linarith
    have h_b_zero : b = 0 := by
      linarith
    have h1 : b + c = 0 := by
      linarith [h_b_zero, h]
    contradiction

  have eq4 : 1 / a = 2 := by
    have h6 : a ≠ 0 := ha1
    have h7 : 1 / a + 1 / b = 3 := by
      have h8 : 3 * a * b = a + b := eq1
      have h10 : a * b ≠ 0 := by
        apply mul_ne_zero
        · exact ha1
        · exact hb1
      field_simp at h8 ⊢
      nlinarith
    have h8 : 1 / b + 1 / c = 4 := by
      have h9 : 4 * b * c = b + c := eq2
      have h12 : b * c ≠ 0 := by
        apply mul_ne_zero
        · exact hb1
        · exact hc1
      field_simp at h9 ⊢
      nlinarith
    have h9 : 1 / c + 1 / a = 5 := by
      have h11 : 5 * c * a = c + a := eq3
      have h13 : c * a ≠ 0 := by
        apply mul_ne_zero
        · exact hc1
        · exact ha1
      field_simp at h11 ⊢
      nlinarith
    linarith [h7, h8, h9]

  have eq5 : 1 / b = 1 := by
    have h6 : a ≠ 0 := ha1
    have h7 : 1 / a + 1 / b = 3 := by
      have h8 : 3 * a * b = a + b := eq1
      have h10 : a * b ≠ 0 := by
        apply mul_ne_zero
        · exact ha1
        · exact hb1
      field_simp at h8 ⊢
      nlinarith
    have h8 : 1 / b + 1 / c = 4 := by
      have h9 : 4 * b * c = b + c := eq2
      have h12 : b * c ≠ 0 := by
        apply mul_ne_zero
        · exact hb1
        · exact hc1
      field_simp at h9 ⊢
      nlinarith
    have h9 : 1 / c + 1 / a = 5 := by
      have h11 : 5 * c * a = c + a := eq3
      have h13 : c * a ≠ 0 := by
        apply mul_ne_zero
        · exact hc1
        · exact ha1
      field_simp at h11 ⊢
      nlinarith
    linarith [h7, h8, h9]

  have eq6 : 1 / c = 3 := by
    have h6 : a ≠ 0 := ha1
    have h7 : 1 / a + 1 / b = 3 := by
      have h8 : 3 * a * b = a + b := eq1
      have h10 : a * b ≠ 0 := by
        apply mul_ne_zero
        · exact ha1
        · exact hb1
      field_simp at h8 ⊢
      nlinarith
    have h8 : 1 / b + 1 / c = 4 := by
      have h9 : 4 * b * c = b + c := eq2
      have h12 : b * c ≠ 0 := by
        apply mul_ne_zero
        · exact hb1
        · exact hc1
      field_simp at h9 ⊢
      nlinarith
    have h9 : 1 / c + 1 / a = 5 := by
      have h11 : 5 * c * a = c + a := eq3
      have h13 : c * a ≠ 0 := by
        apply mul_ne_zero
        · exact hc1
        · exact ha1
      field_simp at h11 ⊢
      nlinarith
    linarith [h7, h8, h9]

  have ha2 : a = 1 / 2 := by
    field_simp at eq4 ⊢
    linarith

  have hb2 : b = 1 := by
    field_simp at eq5 ⊢
    linarith

  have hc2 : c = 1 / 3 := by
    field_simp at eq6 ⊢
    linarith

  rw [ha2, hb2, hc2]
  norm_num
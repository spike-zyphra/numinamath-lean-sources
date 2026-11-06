import Mathlib

theorem algebra_13739 (x y : ℝ) (h₁ : Real.sin x / Real.sin y = 3) (h₂ : Real.cos x / Real.cos y = 1 / 2) :
    Real.sin (2 * x) / Real.sin (2 * y) + Real.cos (2 * x) / Real.cos (2 * y) = 49 / 58 := by

  have h3 : Real.sin y ≠ 0 := by
    by_contra h
    have h4 : Real.sin x / Real.sin y = 0 := by
      rw [h]
      norm_num
    linarith

  have h4 : Real.cos y ≠ 0 := by
    by_contra h
    have h5 : Real.cos x / Real.cos y = 0 := by
      rw [h]
      norm_num
    linarith

  have h5 : Real.sin x = 3 * Real.sin y := by
    have h6 : Real.sin y ≠ 0 := h3
    field_simp [h6] at h₁ ⊢
    linarith

  have h6 : Real.cos x = (1 / 2) * Real.cos y := by
    have h7 : Real.cos y ≠ 0 := h4
    field_simp [h7] at h₂ ⊢
    linarith

  have h7 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  rw [h5, h6] at h7

  have h8 : Real.sin y ^ 2 = 3 / 35 := by
    have h9 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    nlinarith [h7, h9]

  have h9 : Real.cos y ^ 2 = 32 / 35 := by
    have h9 : Real.sin y ^ 2 + Real.cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y
    nlinarith [h7, h9, h8]

  have h10 : Real.sin (2 * x) = 3 * (Real.sin y * Real.cos y) := by
    have h11 : Real.sin (2 * x) = 2 * Real.sin x * Real.cos x := by
      rw [Real.sin_two_mul]
    rw [h11, h5, h6]
    ring

  have h11 : Real.sin (2 * y) = 2 * Real.sin y * Real.cos y := by
    rw [Real.sin_two_mul]

  have h12 : Real.sin (2 * x) / Real.sin (2 * y) = 3 / 2 := by
    rw [h10, h11]
    have h14 : Real.sin y ≠ 0 := h3
    have h15 : Real.cos y ≠ 0 := h4
    field_simp [h14, h15]
    <;> nlinarith

  have h13 : Real.cos (2 * x) = (1 / 4) * Real.cos y ^ 2 - 9 * Real.sin y ^ 2 := by 
    have h14 : Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 := by
      rw [Real.cos_two_mul]
      <;> rw [Real.cos_sq']
      <;> ring
    rw [h14, h5, h6]
    ring

  have h14 : Real.cos (2 * y) = Real.cos y ^ 2 - Real.sin y ^ 2 := by
    rw [Real.cos_two_mul]
    <;> rw [Real.cos_sq']
    <;> ring

  have h15 : Real.cos (2 * x) / Real.cos (2 * y) = -19 / 29 := by
    rw [h13, h14]
    have h17 : Real.cos y ^ 2 = 32 / 35 := h9
    have h18 : Real.sin y ^ 2 = 3 / 35 := h8
    rw [h17, h18]
    field_simp [h4]
    <;> nlinarith

  linarith [h12, h15]
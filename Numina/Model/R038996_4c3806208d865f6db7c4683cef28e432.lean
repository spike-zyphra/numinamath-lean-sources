import Mathlib

open Real Set
open scoped Real

theorem algebra_207176 {x y : ℝ} (h₀ : sin x / sin y = 3) (h₁ : cos x / cos y = 1 / 2) :
    sin (2 * x) / sin (2 * y) + cos (2 * x) / cos (2 * y) = 49 / 58 := by

  have h2 : sin y ≠ 0 := by
    by_contra h
    have : sin x / sin y = 0 := by
      rw [h]
      norm_num
    linarith

  have h3 : cos y ≠ 0 := by
    by_contra h
    have : cos x / cos y = 0 := by
      rw [h]
      norm_num
    linarith

  have h4 : sin x = 3 * sin y := by 
    have h5 : sin y ≠ 0 := h2
    field_simp [h5] at h₀ 
    linarith

  have h6 : cos x = (1 / 2) * cos y := by 
    have h7 : cos y ≠ 0 := h3
    field_simp [h7] at h₁
    linarith

  have h7 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h8 : sin y ^ 2 + cos y ^ 2 = 1 := Real.sin_sq_add_cos_sq y

  have h9 : (3 * sin y) ^ 2 + ((1 / 2) * cos y) ^ 2 = 1 := by 
    rw [show sin x = 3 * sin y by linarith [h4] ] at h7
    rw [show cos x = (1 / 2) * cos y by linarith [h6] ] at h7
    linarith

  have h10 : cos y ^ 2 = 32 / 35 := by 
    nlinarith

  have h11 : sin y ^ 2 = 3 / 35 := by 
    nlinarith

  have h12 : sin (2 * x) = 2 * sin x * cos x := by 
    rw [sin_two_mul]

  have h13 : sin (2 * y) = 2 * sin y * cos y := by 
    rw [sin_two_mul]

  have h14 : cos (2 * x) = 2 * cos x ^ 2 - 1 := by 
    rw [cos_two_mul]

  have h15 : cos (2 * y) = 2 * cos y ^ 2 - 1 := by 
    rw [cos_two_mul]

  have h16 : sin (2 * x) = 3 * (sin y * cos y) := by 
    rw [h12, h4, h6]
    ring

  have h17 : sin (2 * y) = 2 * (sin y * cos y) := by 
    rw [h13]
    all_goals ring

  have h18 : cos (2 * x) = (1 / 2) * cos y ^ 2 - 1 := by 
    rw [h14, h6]
    ring_nf

  have h20 : cos (2 * y) ≠ 0 := by 
    have hcosne : cos y ^ 2 = 32 / 35 := h10
    have hne : 2 * cos y ^ 2 - 1 ≠ 0 := by
      rw [show cos y ^ 2 = 32 / 35 by linarith [hcosne]]
      norm_num
    have : cos (2 * y) = 2 * cos y ^ 2 - 1 := h15
    rw [this]
    exact hne

  have h21 : sin (2 * y) ≠ 0 := by 
    have h2 : sin y ≠ 0 := h2
    have h3 : cos y ≠ 0 := h3
    have : sin (2 * y) = 2 * (sin y * cos y) := h17
    rw [this]
    by_contra h0
    have : sin y * cos y = 0 := by 
      linarith
    cases' (mul_eq_zero.mp this) with h22 h23
    · -- sin y = 0
      exfalso
      apply h2
      linarith
    · -- cos y = 0
      exfalso
      apply h3
      linarith

  have h22 : sin (2 * x) / sin (2 * y) = 3 / 2 := by 
    rw [h16, h17]
    have hne : sin y * cos y ≠ 0 := by 
      apply mul_ne_zero
      exact h2
      exact h3
    field_simp [hne]
    <;> nlinarith

  have h23 : cos (2 * x) / cos (2 * y) = -19 / 29 := by 
    rw [h18, h15]
    have hcosne : cos y ^ 2 = 32 / 35 := h10
    rw [hcosne]
    norm_num

  rw [h22, h23]
  all_goals norm_num
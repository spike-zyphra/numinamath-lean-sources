import Mathlib

theorem algebra_224084 (x : ℝ) (h : Real.tan x + 1 / Real.tan x = 8) :
    Real.sqrt ((1 / Real.cos x)^2 + (1 / Real.sin x)^2 - (1 / 2) * (1 / Real.cos x) * (1 / Real.sin x)) = 2 * Real.sqrt 15 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by 
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at h
  have h1 : Real.sin x ≠ 0 := by
    by_contra h1
    have h2 : Real.sin x / Real.cos x + 1 / (Real.sin x / Real.cos x) = 0 := by 
      rw [h1]
      norm_num [h1]
    rw [h2] at h
    norm_num [h1] at h
  have h2 : Real.cos x ≠ 0 := by 
    by_contra h2
    have h3 : Real.sin x / Real.cos x + 1 / (Real.sin x / Real.cos x) = 0 := by 
      rw [h2]
      norm_num [h2]
    rw [h3] at h
    norm_num [h2] at h
  have h3 : Real.sin x * Real.cos x = 1 / 8 := by 
    field_simp [h1, h2] at h 
    nlinarith [Real.sin_sq_add_cos_sq x]
  have h4 : (1 / Real.cos x) ^ 2 + (1 / Real.sin x) ^ 2 = 64 := by 
    have h5 : Real.sin x * Real.cos x = 1 / 8 := h3
    have h5' : (Real.sin x) * (Real.cos x) = 1 / 8 := h3
    have h6 : (1 / Real.cos x) ^ 2 + (1 / Real.sin x) ^ 2 = (Real.sin x ^ 2 + Real.cos x ^ 2) / (Real.sin x ^ 2 * Real.cos x ^ 2) := by
      field_simp [h1, h2]
      <;> nlinarith
    have h7 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq x
    rw [h6, h7]
    have h8 : Real.sin x ^ 2 * Real.cos x ^ 2 = (1 / 64) := by
      have h5' : Real.sin x * Real.cos x = 1 / 8 := h3
      nlinarith [sq_pos_of_ne_zero h1, sq_pos_of_ne_zero h2]
    rw [h8]
    norm_num
  have h5 : (1 / Real.cos x) * (1 / Real.sin x) = 8 := by 
    have h6 : Real.sin x * Real.cos x = 1 / 8 := h3
    field_simp [h1, h2] at *
    <;> nlinarith [h6]
  have h6 : (1 / Real.cos x)^2 + (1 / Real.sin x)^2 - (1 / 2) * (1 / Real.cos x) * (1 / Real.sin x) = 60 := by
    nlinarith [h4, h5]
  rw [h6]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  <;> ring_nf
  <;> norm_num
  <;> ring_nf
  <;> norm_num
import Mathlib

open Real Set
open scoped Real

theorem algebra_254727 (x : ℝ) :
  sin x * cos x + (sin x) ^ 3 * (cos x) + (sin x) ^ 5 / cos x = tan x := by
  by_cases h : cos x = 0 
  · -- cos x = 0
    have htan : tan x = 0 := by 
      rw [tan_eq_sin_div_cos]
      norm_num [h]
    have h1 : sin x * cos x + (sin x) ^ 3 * (cos x) + (sin x) ^ 5 / cos x = 0 := by
      rw [h]
      norm_num
    rw [h1, htan]
  · -- cos x ≠ 0
    have htan : tan x = sin x / cos x := by 
      rw [tan_eq_sin_div_cos]
    rw [htan]
    have h1 : cos x ≠ 0 := h
    field_simp [h1]
    have h2 : sin x ^ 2 = 1 - cos x ^ 2 := by
      have h1 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x 
      linarith 
    have h3 : sin x ^ 4 = (1 - cos x ^ 2) ^ 2 := by 
      calc 
        sin x ^ 4 = (sin x ^ 2) ^ 2 := by ring 
        _ = (1 - cos x ^ 2) ^ 2 := by rw [h2] 
    have h4 : sin x ^ 6 = (1 - cos x ^ 2) ^ 3 := by 
      calc 
        sin x ^ 6 = (sin x ^ 2) ^ 3 := by ring 
        _ = (1 - cos x ^ 2) ^ 3 := by rw [h2] 
    have h5 : sin x ^ 2 = 1 - cos x ^ 2 := h2 
    nlinarith [sq_nonneg (sin x ^ 2 - (1 - cos x ^ 2)), sq_nonneg (sin x * cos x), 
      sq_nonneg (sin x ^ 2 - 1), sq_nonneg (cos x ^ 2 - 1), 
      Real.sin_sq_add_cos_sq x, 
      sq_nonneg (sin x ^ 2 - cos x ^ 2), 
      sq_nonneg (sin x * (1 - cos x ^ 2)), sq_nonneg (cos x ^ 2 - sin x ^ 2) 
    ]
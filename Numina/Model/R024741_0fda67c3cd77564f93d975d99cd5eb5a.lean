import Mathlib

open Real Set
open scoped Real

theorem calculus_22208 {x : ℝ} (hx : 1 / cos x - tan x = 2) :
    1 / cos x + tan x = 1 / 2 := by
  have h1 : cos x ≠ 0 := by
    by_contra h
    have h2 : 1 / cos x = 0 := by
      rw [h]
      norm_num
    have h3 : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      rw [h]
      norm_num
      all_goals linarith
    rw [h2, h3] at hx
    all_goals linarith

  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have h4 : (1 / cos x) ^ 2 - (tan x) ^ 2 = 1 := by
    have htan2 : tan x = sin x / cos x := by 
      rw [tan_eq_sin_div_cos]
    rw [htan2]
    have h5 : (1 / cos x) ^ 2 - (sin x / cos x) ^ 2 = 1 := by
      have h6 : cos x ≠ 0 := h1
      field_simp [h6]
      <;> nlinarith [h2]
    linarith [h5]

  have htan2 : tan x = sin x / cos x := by 
    rw [tan_eq_sin_div_cos]

  have h5 : (1 / cos x - tan x) * (1 / cos x + tan x) = 1 := by
    nlinarith [h4, htan2]

  have h7 : (1 / cos x - tan x) = 2 := by linarith [hx]

  rw [h7] at h5
  have h8 : (1 / cos x + tan x) = 1 / 2 := by 
    nlinarith

  linarith [h8]
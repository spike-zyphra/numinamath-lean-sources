import Mathlib

open Real Set
open scoped Real

theorem algebra_2901 (x : ℝ) :
  sin x ^ 2 * tan x + cos x ^ 2 / tan x + 2 * sin x * cos x = tan x + 1 / tan x := by
  have htan : tan x = sin x / cos x := by
    rw [tan_eq_sin_div_cos]
  rw [htan]
  by_cases h1 : sin x = 0
  · -- sin x = 0
    rw [h1]
    norm_num
  · -- sin x ≠ 0
    have h1' : sin x ≠ 0 := h1
    by_cases h2 : cos x = 0
    · -- cos x = 0
      rw [h2]
      norm_num [h1']
    · -- cos x ≠ 0
      have h2' : cos x ≠ 0 := h2
      field_simp [h1', h2']
      <;> nlinarith [Real.sin_sq_add_cos_sq x, sq_nonneg (sin x ^ 2 - cos x ^ 2), sq_nonneg (sin x - cos x), sq_nonneg (sin x + cos x), Real.sin_sq_add_cos_sq x, sq_pos_of_ne_zero (show sin x ≠ 0 by assumption), sq_pos_of_ne_zero (show cos x ≠ 0 by assumption), Real.sin_sq_add_cos_sq x]
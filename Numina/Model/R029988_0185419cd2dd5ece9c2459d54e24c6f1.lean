import Mathlib

open Real Set
open scoped Real

theorem algebra_13390 (x : ℝ) (hx : tan x = 2 / sqrt 7) :
    1 - sin (2 * x) = 1 - 4 * sqrt 7 / 11 := by
  have htan : tan x = sin x / cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at hx

  have hcos : cos x ≠ 0 := by
    by_contra h
    rw [h] at hx
    field_simp at hx
    all_goals
      norm_num at hx
      all_goals linarith

  have h1 : sin x = 2 / sqrt 7 * cos x := by
    field_simp [hcos] at hx ⊢
    <;> nlinarith

  have h2 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  rw [h1] at h2

  have h3 : cos x ^ 2 = 7 / 11 := by
    have h4 : (2 / sqrt 7 * cos x) ^ 2 + cos x ^ 2 = 1 := by
      linarith
    have h5 : (2 / sqrt 7 * cos x) ^ 2 = (4 / 7) * cos x ^ 2 := by
      calc
        (2 / sqrt 7 * cos x) ^ 2
          = (2 / sqrt 7) ^ 2 * cos x ^ 2 := by ring_nf
        _ = (4 / 7) * cos x ^ 2 := by
          have h6 : (sqrt 7) ^ 2 = 7 := Real.sq_sqrt (by linarith)
          field_simp [h6]
          <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7)]

    rw [h5] at h4
    nlinarith

  have hsin2x : sin (2 * x) = 2 * sin x * cos x := by
    rw [Real.sin_two_mul]

  rw [hsin2x, h1]

  have h8 : (sqrt 7) ^ 2 = 7 := Real.sq_sqrt (show (0 : ℝ) ≤ 7 by linarith)
  have h9 : (2 / sqrt 7 : ℝ) = 2 * sqrt 7 / 7 := by
    field_simp [Real.sqrt_ne_zero']
    <;> nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7)]

  rw [h9]

  nlinarith [Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 7), Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ 7 by linarith)]
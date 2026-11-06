import Mathlib

open Real Set
open scoped Real

theorem calculus_16519 (x : ℝ) (hx : x ≠ π / 2) (h : 1 / cos x + tan x = 4 / 3) :
    sin x = 7 / 25 := by

  have h1 : cos x ≠ 0 := by
    by_contra h1
    have htan : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h1]
    have hsec : 1 / cos x = 0 := by
      simp [h1]
    rw [htan, hsec] at h
    norm_num at h

  have h2 : tan x = sin x / cos x := by
    simp [tan_eq_sin_div_cos]

  rw [h2] at h

  have eq1 : (1 + sin x) / cos x = 4 / 3 := by
    field_simp [h1] at h ⊢
    linarith

  have eq2 : 3 * (1 + sin x) = 4 * cos x := by
    field_simp [h1] at eq1 ⊢
    linarith

  have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x

  have eq3 : cos x = (3 + 3 * sin x) / 4 := by
    linarith

  rw [eq3] at h4

  have h5 : 25 * (sin x) ^ 2 + 18 * (sin x) - 7 = 0 := by
    nlinarith

  have h6 : (sin x - 7 / 25) * (sin x + 1) = 0 := by
    nlinarith

  cases' (mul_eq_zero.mp h6) with h7 h8

  · -- sin x = 7 / 25
    linarith

  · -- sin x = -1
    have eq4 : sin x = -1 := by linarith

    have eq5 : cos x = 0 := by
      rw [eq3]
      nlinarith [eq4]

    contradiction
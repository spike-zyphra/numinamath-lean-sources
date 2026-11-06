import Mathlib

open Real Set
open scoped Real

theorem algebra_188056 {x : ℝ} (hx : 20 * sin x = 22 * cos x) :
    ⌊((1 / (sin x * cos x) - 1)^7 : ℝ)⌋ = 1 := by
  have h1 : sin x ≠ 0 := by
    by_contra h
    rw [h] at hx
    have h2 : cos x = 0 := by nlinarith [Real.cos_sq_add_sin_sq x]
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h, h2] at h3
    norm_num at h3
  have h2 : cos x ≠ 0 := by
    by_contra h
    rw [h] at hx
    have h1 : sin x = 0 := by nlinarith [Real.cos_sq_add_sin_sq x]
    have h3 : cos x ^ 2 + sin x ^ 2 = 1 := Real.cos_sq_add_sin_sq x
    rw [h, h1] at h3
    norm_num at h3
  have h3 : sin x = (11 / 10) * cos x := by
    linarith [hx]
  have h4 : sin x ^ 2 + cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h3] at h4
  have h5 : cos x ^ 2 = 100 / 221 := by
    nlinarith
  have h6 : sin x * cos x = 110 / 221 := by
    have h7 : sin x * cos x = (11 / 10) * cos x ^ 2 := by
      rw [h3]
      ring
    rw [h7, h5]
    norm_num
  have h8 : (1 / (sin x * cos x) - 1 : ℝ) = (111 / 110 : ℝ) := by
    rw [show sin x * cos x = (110 / 221 : ℝ) by linarith [h6]]
    norm_num
  rw [h8]
  norm_num [Int.floor_eq_iff]
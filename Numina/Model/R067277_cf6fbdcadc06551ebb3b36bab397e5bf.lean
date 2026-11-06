import Mathlib

open Real Set
open scoped Real

theorem algebra_254693 {x y : ℝ} (h₀ : cos x + cos y = 1 / 2) (h₁ : sin x + sin y = 1 / 3) :
    cos (x - y) = -59 / 72 := by
  have h2 : cos (x - y) = cos x * cos y + sin x * sin y := by
    rw [cos_sub]

  have h3 : (cos x + cos y) ^ 2 = 1 / 4 := by
    rw [h₀]
    all_goals norm_num

  have h4 : (sin x + sin y) ^ 2 = 1 / 9 := by
    rw [h₁]
    all_goals norm_num

  have h5 : (cos x + cos y) ^ 2 = cos x ^ 2 + 2 * (cos x * cos y) + cos y ^ 2 := by
    ring

  have h6 : (sin x + sin y) ^ 2 = sin x ^ 2 + 2 * (sin x * sin y) + sin y ^ 2 := by
    ring

  rw [h5] at h3
  rw [h6] at h4

  have h7 : cos x ^ 2 + sin x ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq x

  have h8 : cos y ^ 2 + sin y ^ 2 = 1 := by
    exact Real.cos_sq_add_sin_sq y

  have h11 : cos x * cos y + sin x * sin y = -59 / 72 := by
    nlinarith [h3, h4, h7, h8]

  rw [h2]
  linarith [h11]
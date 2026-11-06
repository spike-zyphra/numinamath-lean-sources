import Mathlib

open Real Set
open scoped Real

theorem algebra_3301 (θ : ℝ) (h : cos θ = 1 / 3) :
    2 / (1 - sin θ) + 2 / (1 + sin θ) = 36 := by
  have h1 : sin θ ^ 2 = 8 / 9 := by
    have h2 : sin θ ^ 2 + cos θ ^ 2 = 1 := by
      exact Real.sin_sq_add_cos_sq θ
    rw [h] at h2
    nlinarith
  have h2 : 1 - sin θ ≠ 0 := by
    by_contra h3
    have h4 : sin θ = 1 := by linarith
    have h5 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq θ
    rw [h4] at h5
    rw [h] at h5
    norm_num at h5
  have h3 : 1 + sin θ ≠ 0 := by
    by_contra h4
    have h5 : sin θ = -1 := by linarith
    have h6 : cos θ ^ 2 + sin θ ^ 2 = 1 := by
      exact Real.cos_sq_add_sin_sq θ
    rw [h5] at h6
    rw [h] at h6
    norm_num at h6
  have h4 : (1 - sin θ) * (1 + sin θ) = 1 / 9 := by
    have h5 : sin θ ^ 2 = 8 / 9 := h1
    calc
      (1 - sin θ) * (1 + sin θ) = 1 - sin θ ^ 2 := by ring
      _ = 1 - (8 / 9) := by rw [h5]
      _ = 1 / 9 := by norm_num
  field_simp [(show 1 - sin θ ≠ 0 by exact h2), (show 1 + sin θ ≠ 0 by exact h3)]
  nlinarith [h4, h1, Real.sin_sq_add_cos_sq θ, h]
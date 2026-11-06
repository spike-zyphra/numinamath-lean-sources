import Mathlib

open Real Set
open scoped Real

theorem algebra_192431 (θ : ℝ) (h : sin θ = 3 / 5) (a : ℝ)
  (ha : a = sqrt (tan θ ^ 2 + 1)) : a = 5 / 4 := by 
  have h1 : cos θ ^ 2 = 1 - sin θ ^ 2 := by 
    have h2 : sin θ ^ 2 + cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
    linarith 
  rw [h] at h1
  have h2 : cos θ ^ 2 = 16 / 25 := by 
    rw [h1]
    norm_num 
  have htan_sq : tan θ ^ 2 = 9 / 16 := by
    have htan : tan θ = sin θ / cos θ := by 
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    have hcos_sq : cos θ ≠ 0 := by nlinarith [Real.cos_sq_add_sin_sq θ, h]
    have hsin_sq : sin θ = 3 / 5 := h 
    field_simp [hcos_sq]
    nlinarith [hsin_sq, h2]
  have htan_sq_add_1 : tan θ ^ 2 + 1 = 25 / 16 := by 
    rw [htan_sq]
    norm_num 
  rw [ha, htan_sq_add_1]
  rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
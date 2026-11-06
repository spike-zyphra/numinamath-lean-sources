import Mathlib
open Real

theorem algebra_5650 (x : ℝ) (hx : tan x = 5) : sin x * cos x = 5 / 26 := by 
  have h1 : cos x ≠ 0 := by
    by_contra h
    have h2 : tan x = 0 := by
      rw [tan_eq_sin_div_cos]
      simp [h]
    rw [h2] at hx
    norm_num at hx 
  have h2 : sin x = 5 * cos x := by
    have htan : tan x = sin x / cos x := by
      rw [tan_eq_sin_div_cos]
    rw [htan] at hx
    field_simp [h1] at hx ⊢
    linarith 
  have h3 : sin x ^ 2 + cos x ^ 2 = 1 := by 
    exact Real.sin_sq_add_cos_sq x 
  rw [h2] at h3 
  have h4 : cos x ^ 2 = 1 / 26 := by 
    nlinarith 
  calc 
    sin x * cos x = (5 * cos x) * cos x := by rw [h2]
    _ = 5 * (cos x ^ 2) := by ring 
    _ = 5 * (1 / 26) := by rw [h4]
    _ = 5 / 26 := by norm_num
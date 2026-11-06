import Mathlib

theorem algebra_5339 (x : Real) (h : Real.tan x = 8) :
    (Real.sin x - 3 * Real.cos x) * Real.sin x = 8 / 13 := by
  have htan : Real.tan x = Real.sin x / Real.cos x := by
    rw [Real.tan_eq_sin_div_cos]
  rw [htan] at h
  have h1 : Real.cos x ≠ 0 := by
    by_contra h2
    rw [h2] at h
    norm_num at h
  have h2 : Real.sin x = 8 * Real.cos x := by
    field_simp [h1] at h
    linarith
  have h3 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  rw [h2] at h3
  have h4 : Real.cos x ^ 2 = 1 / 65 := by
    nlinarith
  have h5 : Real.sin x - 3 * Real.cos x = 5 * Real.cos x := by
    linarith [h2]
  calc
    (Real.sin x - 3 * Real.cos x) * Real.sin x
        = (5 * Real.cos x) * Real.sin x := by rw [h5]
    _ = 5 * Real.cos x * Real.sin x := by ring
    _ = 5 * Real.cos x * (8 * Real.cos x) := by rw [h2]
    _ = 5 * 8 * (Real.cos x)^2 := by ring
    _ = 40 * (Real.cos x)^2 := by ring
    _ = 40 * (1 / 65) := by rw [h4]
    _ = 40 / 65 := by ring
    _ = 8 / 13 := by norm_num
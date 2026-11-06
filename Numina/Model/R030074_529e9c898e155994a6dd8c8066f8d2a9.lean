import Mathlib

theorem algebra_3517 (x : ℝ) (hx : Real.cos x = 3 / 4) :
    (Real.tan x ^ 2 * (1 - Real.sin x) * (Real.sin x + 1)) / (1 + Real.cos x) = 1 / 4 := by
  have h1 : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 := Real.sin_sq_add_cos_sq x
  have h2 : Real.sin x ^ 2 = 7 / 16 := by
    rw [show Real.cos x = 3 / 4 by linarith [hx]] at h1
    nlinarith
  have h3 : Real.cos x ^ 2 = 9 / 16 := by
    rw [hx]
    norm_num
  have h4 : Real.tan x ^ 2 = 7 / 9 := by
    have htan : Real.tan x = Real.sin x / Real.cos x := by
      rw [Real.tan_eq_sin_div_cos]
    rw [htan]
    have h5 : Real.cos x ≠ 0 := by
      rw [hx]
      norm_num
    field_simp [h5]
    <;> nlinarith [h2, h3]
  have h5 : (1 - Real.sin x) * (Real.sin x + 1) = Real.cos x ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq x, h2]
  have htan2 : Real.tan x ^ 2 * (1 - Real.sin x) * (Real.sin x + 1) = Real.sin x ^ 2 := by
    calc
      Real.tan x ^ 2 * (1 - Real.sin x) * (Real.sin x + 1)
        = Real.tan x ^ 2 * ((1 - Real.sin x) * (Real.sin x + 1)) := by ring
      _ = Real.tan x ^ 2 * (Real.cos x ^ 2) := by rw [h5]
      _ = Real.sin x ^ 2 := by
        rw [h4]
        have hc : Real.cos x ^ 2 = 9 / 16 := by
          nlinarith [hx]
        rw [hc]
        nlinarith [h2]
  have h7 : (1 + Real.cos x) = 7 / 4 := by
    rw [hx]
    norm_num
  rw [show Real.tan x ^ 2 * (1 - Real.sin x) * (Real.sin x + 1) = Real.sin x ^ 2 by linarith [htan2]]
  rw [h7]
  rw [h2]
  all_goals norm_num
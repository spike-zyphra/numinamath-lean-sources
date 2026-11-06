import Mathlib

open Real

theorem algebra_6719 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : a^2 + b^2 = 88) (h₁ : a = 11 - b) : a * b = 33 / 2 := by
  rw [h₁] at h₀
  have h2 : (11 - b) ^ 2 + b ^ 2 = 88 := h₀
  have h3 : 2 * b ^ 2 - 22 * b + 33 = 0 := by
    nlinarith
  have h4 : b ^ 2 = 11 * b - 33 / 2 := by 
    nlinarith
  have h5 : a * b = b * (11 - b) := by
    rw [h₁]
    all_goals ring
  rw [h5]
  have h6 : b * (11 - b) = 33 / 2 := by
    nlinarith [h4]
  linarith [h6]
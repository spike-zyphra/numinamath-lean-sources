import Mathlib

theorem other_172196 (length width : ℝ) (h₀ : length = 360) (h₁ : width = 220)
    (h₂ : 58 * length * width / (10 * 105) = 40 * x) :
    x ≥ 22 := by
  rw [h₀, h₁] at h₂
  norm_num at h₂
  linarith
import Mathlib

theorem algebra_202281 {x y z t : ℝ} (h : x * y * z * t = 1) (h₁ : 1 + x + x * y + x * y * z ≠ 0)
    (h₂ : 1 + y + y * z + y * z * t ≠ 0) (h₃ : 1 + z + z * t + z * t * x ≠ 0)
    (h₄ : 1 + t + t * x + t * x * y ≠ 0) :
    1 / (1 + x + x * y + x * y * z) +
    1 / (1 + y + y * z + y * z * t) +
    1 / (1 + z + z * t + z * t * x) +
    1 / (1 + t + t * x + t * x * y) = 1 := by
  have k₁ : x ≠ 0 := by
    intro k
    simp [k] at h
  have k₂ : x * y ≠ 0 := by
    intro k
    simp [k] at h
  have k₃ : x * y * z ≠ 0 := by
    intro k
    simp [k] at h
  calc 1 / (1 + x + x * y + x * y * z) + 1 / (1 + y + y * z + y * z * t) + 1 / (1 + z + z * t + z * t * x) + 1 / (1 + t + t * x + t * x * y)
    _ = 1 / (1 + x + x * y + x * y * z) + x / ((1 + y + y * z + y * z * t) * x) + (x * y) / ((1 + z + z * t + z * t * x) * (x * y)) + (x * y * z) / ((1 + t + t * x + t * x * y) * (x * y * z)) := by simp [div_mul_cancel_right₀, k₁, k₂, k₃]
    _ = 1 / (1 + x + x * y + x * y * z) + x / (1 + x + x * y + x * y * z) + (x * y) / (1 + x + x * y + x * y * z) + (x * y * z) / (1 + x + x * y + x * y * z) := by
      congr
      . linear_combination h
      . linear_combination (x + 1) * h
      . linear_combination (x * y + x + 1) * h
    _ = (1 + x + x * y + x * y * z) / (1 + x + x * y + x * y * z) := by rw [add_div, add_div, add_div]
    _ = 1 := div_self h₁

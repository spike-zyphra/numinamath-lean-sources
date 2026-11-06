import Mathlib

theorem algebra_985 {a b : ℝ} (h₀ : a + b = 3) (h₁ : a ^ 2 * b + a * b ^ 2 = -30) :
    a ^ 2 - a * b + b ^ 2 + 11 = 50 := by
  have h2 : a * b = -10 := by
    have h3 : a ^ 2 * b + a * b ^ 2 = a * b * (a + b) := by
      ring
    rw [h3] at h₁
    rw [h₀] at h₁
    linarith

  have h4 : a ^ 2 - a * b + b ^ 2 = (a + b) ^ 2 - 3 * (a * b) := by
    ring

  rw [h4, h₀, h2]
  norm_num
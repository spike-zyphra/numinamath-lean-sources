import Mathlib

theorem algebra_317612 {a b c x : ℝ} (h₀ : a * b * c = 1) (h₁ : 1 + a + a * b ≠ 0) (h₂ : 1 + b + b * c ≠ 0) (h₃ : 1 + c + a * c ≠ 0) (h : x / (1 + a + a * b) + x / (1 + b + b * c) + x / (1 + c + a * c) = 2003) :
    x = 2003 := by
  have lem : 1 / (1 + a + a * b) + 1 / (1 + b + b * c) + 1 / (1 + c + a * c) = 1 := by
    field_simp
    linear_combination (- b * c * a - b * c - b * a - c * a - b - c - a - 2) * h₀
  calc
    x = x * (1 / (1 + a + a * b) + 1 / (1 + b + b * c) + 1 / (1 + c + a * c)) := by rw [lem]; simp
    _ = x / (1 + a + a * b) + x / (1 + b + b * c) + x / (1 + c + a * c) := by ring
    _ = 2003 := h

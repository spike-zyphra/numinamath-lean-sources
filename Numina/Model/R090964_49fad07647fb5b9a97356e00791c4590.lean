import Mathlib

theorem algebra_158953 (a b c d e : ℝ)
    (h₀ : a = 92) (h₁ : b = 94) (h₂ : c = 103) (h₃ : d = 105) (h₄ : e = 106) :
    (a + b + c + d + e) / 5 = 100 ∧
    ((a - 100) ^ 2 + (b - 100) ^ 2 + (c - 100) ^ 2 + (d - 100) ^ 2 + (e - 100) ^ 2) / 5 = 34 ∧
    ((a - 100) ^ 2 + (b - 100) ^ 2 + (c - 100) ^ 2 + (d - 100) ^ 2 + (e - 100) ^ 2) / 4 = 42.5 := by
  constructor
  · -- Calculate the mean
    rw [h₀, h₁, h₂, h₃, h₄]
    norm_num
  constructor
  · -- Calculate the uncorrected variance
    rw [h₀, h₁, h₂, h₃, h₄]
    norm_num
  · -- Calculate the corrected variance
    rw [h₀, h₁, h₂, h₃, h₄]
    norm_num
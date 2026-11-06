import Mathlib

theorem algebra_1086 (a b c : ℝ) (h₀ : a + b - c = 5) (h₁ : a - b + c = 7) :
    a ^ 2 + b ^ 2 + c ^ 2 - 2 * b * c = 37 := by
  have ha : a = 6 := by
    linarith
  have h2 : b - c = -1 := by
    linarith [h₀, ha]
  have h3 : b ^ 2 + c ^ 2 - 2 * b * c = (b - c) ^ 2 := by
    ring
  calc
    a ^ 2 + b ^ 2 + c ^ 2 - 2 * b * c = a^2 + (b^2 + c^2 - 2 * b * c) := by ring
    _ = a^2 + (b - c) ^ 2 := by rw [h3]
    _ = (6 : ℝ) ^ 2 + (-1 : ℝ) ^ 2 := by rw [ha, h2]
    _ = (36 : ℝ) + (1 : ℝ) := by norm_num
    _ = (37 : ℝ) := by norm_num
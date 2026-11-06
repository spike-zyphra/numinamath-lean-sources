import Mathlib

theorem algebra_14881 (m1 m2 b1 b2 : ℝ) (h₀ : m1 = 3) (h₁ : m2 = 5)
    (h₂ : b1 = 15 - 3 * 10) (h₃ : b2 = 15 - 5 * 10) :
    abs (b1 / m1 - b2 / m2) = 2 := by
  rw [h₀, h₁, h₂, h₃]
  norm_num [abs_of_nonneg]
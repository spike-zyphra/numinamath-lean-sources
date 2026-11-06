import Mathlib

theorem algebra_178837 (i j : ℝ) (hi : 0 ≤ i ∧ i ≤ 100) (hj : 0 ≤ j ∧ j ≤ 100)
    (h : (1 + i / 100) * (1 + j / 100) = 1 + (i + j + i * j / 100) / 100) :
    (i + j + i * j / 100) / 100 = (1 + i / 100) * (1 + j / 100) - 1 := by
  linarith
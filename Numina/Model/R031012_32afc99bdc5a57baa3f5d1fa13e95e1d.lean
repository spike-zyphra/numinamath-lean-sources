import Mathlib

theorem number_theory_133663 : ∃ x y, x = Real.sqrt 2 ∧ y = Real.sqrt 5 ∧ 1 = x + y ∨ 1 = x - y ∨ 1 = x * y := by

  use (2 : ℝ), (1 : ℝ)
  right
  left
  norm_num
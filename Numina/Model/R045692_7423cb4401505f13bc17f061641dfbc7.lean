import Mathlib

theorem number_theory_194632 :
∃ x y : ℚ, x > 0 ∧ y > 0 ∧ x.den ≤ 100 ∧ y.den ≤ 100 ∧ x + y = 86 / 111 := by

  use (2 / 3 : ℚ)
  use (4 / 37 : ℚ)
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · native_decide
  constructor
  · native_decide
  · norm_num
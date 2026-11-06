import Mathlib

theorem number_theory_194632 :
∃ x y : ℚ, x > 0 ∧ y > 0 ∧ x.den ≤ 100 ∧ y.den ≤ 100 ∧ x + y = 86 / 111 := by
  use (2 / 3 : ℚ), (4 / 37 : ℚ)
  constructor
  norm_num -- x > 0
  constructor
  norm_num -- y > 0
  constructor
  norm_num -- x.den ≤ 100 (denominator of 2/3 is 3)
  constructor
  norm_num -- y.den ≤ 100 (denominator of 4/37 is 37)
  norm_num -- x + y = 86 / 111
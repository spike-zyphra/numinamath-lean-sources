import Mathlib

theorem algebra_243595 : ∃ x y z : ℚ, x > 0 ∧ y > 0 ∧ z > 0 ∧ x + y + z = 179 / 140 ∧
    x.den = 4 ∧ y.den = 5 ∧ z.den = 7 := by 
  use 1 / 4, 3 / 5, 3 / 7
  constructor
  · norm_num 
  constructor
  · norm_num 
  constructor
  · norm_num 
  constructor
  · norm_num
  constructor
  · norm_num [Rat.den]
  constructor
  · norm_num [Rat.den]
  · norm_num [Rat.den]
import Mathlib

theorem number_theory_287683 : ∃ x y, x > 0 ∧ y > 0 ∧ x + y = 283 ∧ 13 ∣ x ∧ 17 ∣ y := by
  use 130, 153
  constructor
  · norm_num -- shows 130 > 0
  constructor
  · norm_num -- shows 153 > 0
  constructor
  · norm_num -- shows 130 + 153 = 283
  constructor
  · norm_num -- shows 13 divides 130
  · norm_num -- shows 17 divides 153
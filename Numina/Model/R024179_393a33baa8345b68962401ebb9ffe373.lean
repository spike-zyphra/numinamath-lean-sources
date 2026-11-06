import Mathlib

theorem number_theory_52748 :
    ∃ x y, x > 0 ∧ y > 0 ∧ x * y = 3^2008 + 4^2009 ∧ x > 2009^182 ∧ y > 2009^182 := by
  use (3 ^ 1004 + 2 ^ 2009 - 3 ^ 502 * 2 ^ 1005),
    (3 ^ 1004 + 2 ^ 2009 + 3 ^ 502 * 2 ^ 1005)
  norm_num
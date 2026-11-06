import Mathlib

theorem number_theory_121387 :
    ∃ a b, a * b = 3 ^ 2008 + 4 ^ 2009 ∧ a > 0 ∧ b > 0 ∧ a > 2009 ^ 182 ∧ b > 2009 ^ 182 := by
  use (3 ^ 1004 + 2 * 4 ^ 1004 + 3 ^ 502 * 2 ^ 1005), (3 ^ 1004 + 2 * 4 ^ 1004 - 3 ^ 502 * 2 ^ 1005)
  constructor
  · -- Show that the product of the two expressions is 3^2008 + 4^2009
    ring_nf
  constructor
  · -- Show that the first number is positive
    norm_num
  constructor
  · -- Show that the second number is positive
    norm_num
  constructor
  · -- Show that the first number is greater than 2009^182
    norm_num
  · -- Show that the second number is greater than 2009^182
    norm_num
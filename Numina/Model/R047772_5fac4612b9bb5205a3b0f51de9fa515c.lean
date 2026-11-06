import Mathlib
theorem number_theory_609108 : 1007021035035021007001 = 7 ^ 7 * 11 ^ 7 * 13 ^ 7 ∧ Nat.Prime 7 ∧ Nat.Prime 11 ∧ Nat.Prime 13 ∧ 7 ≠ 11 ∧ 7 ≠ 13 ∧ 11 ≠ 13:= by 
  constructor
  · -- Verify the equality
    norm_num
  constructor
  · -- Show that 7 is prime
    norm_num
  constructor
  · -- Show that 11 is prime
    norm_num
  constructor
  · -- Show that 13 is prime
    norm_num
  constructor
  · -- Show that 7 ≠ 11
    norm_num
  constructor
  · -- Show that 7 ≠ 13
    norm_num
  · -- Show that 11 ≠ 13
    norm_num
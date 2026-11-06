import Mathlib

theorem number_theory_4360 : Nat.lcm 31291 38077 ≠ 0 ∧ 31291 * 38077 / Nat.lcm 31291 38077 = 377 := by
  constructor
  · -- Show that Nat.lcm 31291 38077 ≠ 0
    norm_num [Nat.lcm]
  · -- Show that 31291 * 38077 / Nat.lcm 31291 38077 = 377
    norm_num [Nat.lcm]
import Mathlib

theorem number_theory_19373 :
    ∃ a b, a ≠ b ∧ a ∈ Finset.Icc 10 99 ∧ b ∈ Finset.Icc 10 99 ∧
      7 ∣ a ∧ 7 ∣ b ∧ (Nat.digits 10 a).sum = 10 ∧ (Nat.digits 10 b).sum = 10 ∧
      a + b = 119 := by
  use 28, 91
  constructor
  · norm_num
  constructor
  · -- Show that 28 is in the range [10, 99]
    simp [Finset.mem_Icc]
  constructor
  · -- Show that 91 is in the range [10, 99]
    simp [Finset.mem_Icc]
  constructor
  · -- Show that 28 is divisible by 7
    norm_num
  constructor
  · -- Show that 91 is divisible by 7
    norm_num
  constructor
  · -- Show that the digit sum of 28 is 10
    norm_num
  constructor
  · -- Show that the digit sum of 91 is 10
    norm_num
  · -- Show that the sum of 28 and 91 is 119
    norm_num
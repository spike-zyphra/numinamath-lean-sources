import Mathlib

theorem number_theory_211405 : ∃ n, n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).sum = 23 ∧ 23 ∣ n := by
  use 7682
  constructor
  · -- Show 7682 is in the range [1000, 9999]
    simp [Finset.mem_Icc]
  constructor
  · -- Show the sum of digits is 23
    norm_num
  · -- Show 23 divides 7682
    norm_num
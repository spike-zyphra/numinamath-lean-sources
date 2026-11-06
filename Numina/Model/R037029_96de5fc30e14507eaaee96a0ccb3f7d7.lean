import Mathlib

theorem number_theory_35468 :
  ∃ n : ℕ, 2 < n ∧ 1991 ∣ (1999 * 10 ^ n + 91) := by
  use 98
  constructor
  · norm_num
  · native_decide
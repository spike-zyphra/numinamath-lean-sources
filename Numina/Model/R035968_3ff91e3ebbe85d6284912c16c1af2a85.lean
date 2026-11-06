import Mathlib

theorem number_theory_79098 :
    ∃ a b c : ℕ, 1 ≤ a ∧ a < b ∧ b < c ∧ c ≤ 25 ∧
      (Nat.digits 10 (a ^ 6 + 2014)).sum = (Nat.digits 10 (b ^ 6 + 2014)).sum ∧
      (Nat.digits 10 (b ^ 6 + 2014)).sum = (Nat.digits 10 (c ^ 6 + 2014)).sum := by

  use 13
  use 16
  use 22
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · native_decide
  · native_decide
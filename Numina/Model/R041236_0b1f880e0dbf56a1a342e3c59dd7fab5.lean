import Mathlib

theorem number_theory_213754 :
    ∃ n : ℕ, 0 < n ∧ (Nat.factorial n) % 10^100 = 0 ∧ (Nat.factorial n) % 10^101 ≠ 0 := by
  use 406
  constructor
  · norm_num
  constructor
  · native_decide
  · native_decide
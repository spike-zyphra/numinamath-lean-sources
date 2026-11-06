import Mathlib

theorem number_theory_28198 :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ Nat.Coprime m n ∧ 2549 ∣ (25 * 49)^m + 25^n - 2 * 49^n := by
  use 7
  use 13
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num
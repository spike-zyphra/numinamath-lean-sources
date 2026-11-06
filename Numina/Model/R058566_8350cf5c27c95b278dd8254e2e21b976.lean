import Mathlib

theorem algebra_38689 : ∃ m n : ℕ, m > 0 ∧ n > 0 ∧ Nat.Coprime m n ∧
    (1 / 20 - 1 / 21 + 1 / (20 * 21) : ℚ) = m / n := by
  use 1, 210
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num 
  · norm_num
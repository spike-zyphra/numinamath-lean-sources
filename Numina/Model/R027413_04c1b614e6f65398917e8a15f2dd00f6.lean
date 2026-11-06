import Mathlib

theorem number_theory_261390 :
    ∃ a b c d e : ℤ, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ e ∧ b ≠ c ∧ b ≠ d ∧ b ≠ e ∧
      c ≠ d ∧ c ≠ e ∧ d ≠ e ∧ ∃ m n p q r : ℕ, a + b + c + d = m^2 ∧ a + b + c + e = n^2 ∧
      a + b + d + e = p^2 ∧ a + c + d + e = q^2 ∧ b + c + d + e = r^2 := by
  use -45, -9, 19, 39, 51
  constructor
  · -- Show a ≠ b
    norm_num
  constructor
  · -- Show a ≠ c
    norm_num
  constructor
  · -- Show a ≠ d
    norm_num
  constructor
  · -- Show a ≠ e
    norm_num
  constructor
  · -- Show b ≠ c
    norm_num
  constructor
  · -- Show b ≠ d
    norm_num
  constructor
  · -- Show b ≠ e
    norm_num
  constructor
  · -- Show c ≠ d
    norm_num
  constructor
  · -- Show c ≠ e
    norm_num
  constructor
  · -- Show d ≠ e
    norm_num
  · -- Show the existence of m, n, p, q, r such that the equations hold
    use 2, 4, 6, 8, 10
    all_goals norm_num
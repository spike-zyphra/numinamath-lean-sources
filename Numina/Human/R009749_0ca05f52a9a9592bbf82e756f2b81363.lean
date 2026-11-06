import Mathlib

theorem number_theory_200765 :
    ∃ n : ℕ,
      (1989 * 10 ^ (Nat.digits 10 n).length + n) % 1988 = 0 ∧
      (1988 * 10 ^ (Nat.digits 10 n).length + n) % 1989 = 0 := by

  use 856792
  norm_num
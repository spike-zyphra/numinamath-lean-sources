import Mathlib

theorem number_theory_111678 :
    ∃ n : ℕ, n > 1000000 ∧ ∃ m : ℕ, m > 1000000 ∧ n = m + 1 ∧
      ∃ p : ℕ, p^2 = (Nat.digits 10 n).sum ∧ ∃ q : ℕ, q^2 = (Nat.digits 10 m).sum := by 
  use 1000000000 
  constructor
  · norm_num
  use 999999999 
  constructor
  · norm_num 
  constructor
  · norm_num 
  use 1
  constructor
  · native_decide 
  use 9
  · native_decide
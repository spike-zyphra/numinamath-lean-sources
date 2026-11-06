import Mathlib

theorem number_theory_56773 :
    ∃ n : ℕ, 0 < n ∧ (Nat.digits 10 (3 ^ n)).headI = 1 ∧ (Nat.digits 10 (7 ^ n)).headI = 1 ∧
    (Nat.digits 10 (3 ^ n)).tail.headI = 0 ∧ (Nat.digits 10 (7 ^ n)).tail.headI = 0 := by 
  use 20
  constructor
  · norm_num
  constructor
  · native_decide
  constructor
  · native_decide
  constructor
  · native_decide
  · native_decide
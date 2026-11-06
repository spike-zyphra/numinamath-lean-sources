import Mathlib

theorem number_theory_27309 (n : ℕ) (h : (Nat.digits 10 n).contains 1 ∧ (Nat.digits 10 n).contains 3 ∧ (Nat.digits 10 n).contains 7 ∧ (Nat.digits 10 n).contains 9) :
    ∃ m, (Nat.digits 10 m).length = 4 ∧ (Nat.digits 10 m).toFinset = {1, 3, 7, 9} ∧ 7 ∣ m := by 
  use 1379
  constructor
  · -- Check that length is 4
    native_decide
  constructor
  · -- Check that the digits as a finset equals {1, 3, 7, 9}
    native_decide
  · -- Check that 7 divides 1379
    native_decide
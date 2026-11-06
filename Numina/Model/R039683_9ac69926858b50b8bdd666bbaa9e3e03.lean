import Mathlib

theorem number_theory_211461 : ∃ n : ℕ, (Nat.digits 10 n).length = 5 ∧ (Nat.digits 10 n).sum = 31 ∧ 31 ∣ n := by 
  use 93775
  constructor
  · -- Show the length of the digits of 93775 is 5
    native_decide
  constructor
  · -- Show the sum of the digits of 93775 equals 31
    native_decide
  · -- Show 31 divides 93775
    native_decide
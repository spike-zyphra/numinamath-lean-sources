import Mathlib

theorem number_theory_195999 : (Nat.Prime 2 ∧ 2 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 3 ∧ 3 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 5 ∧ 5 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 7 ∧ ¬7 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 11 ∧ ¬11 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 13 ∧ 13 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 109 ∧ 109 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 151 ∧ 151 ∣ 1963^1965 - 1963) ∧
    (Nat.Prime 491 ∧ 491 ∣ 1963^1965 - 1963) := by 
  constructor
  · constructor
    · norm_num
    · norm_num
  constructor
  · constructor
    · norm_num
    · norm_num
  constructor
  · constructor
    · norm_num
    · norm_num
  constructor
  · constructor
    · norm_num
    · native_decide
  constructor
  · constructor
    · norm_num
    · native_decide
  constructor
  · constructor
    · norm_num
    · norm_num
  constructor
  · constructor
    · norm_num
    · norm_num
  constructor
  · constructor
    · norm_num
    · norm_num
  · constructor
    · norm_num
    · norm_num
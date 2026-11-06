import Mathlib

theorem number_theory_161088 :
    ∃ a b c : ℕ, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      (Nat.digits 10 a).length = 3 ∧
      (Nat.digits 10 b).length = 3 ∧
      (Nat.digits 10 c).length = 3 ∧
      (Nat.digits 10 a).toFinset.card = 3 ∧
      (Nat.digits 10 b).toFinset.card = 3 ∧
      (Nat.digits 10 c).toFinset.card = 3 ∧
      (Nat.digits 10 a).toFinset ∪ (Nat.digits 10 b).toFinset ∪ (Nat.digits 10 c).toFinset = {1, 2, 3, 4, 5, 6, 7, 8, 9} ∧
      a * b * c ≡ 0 [MOD 10000] := by
  use 625, 384, 971
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  constructor
  · norm_num
  · native_decide
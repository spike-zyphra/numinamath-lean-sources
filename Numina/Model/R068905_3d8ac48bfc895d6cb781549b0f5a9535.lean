import Mathlib

theorem number_theory_169699 :
    ∃ n : ℕ, (Nat.digits 10 n).length > 0 ∧
      (∀ d ∈ (Nat.digits 10 n), d = 7 ∨ d = 5) ∧
      (∃ k : ℕ, k = (Nat.digits 10 n).length ∧
        (Nat.digits 10 n).count 7 = (Nat.digits 10 n).count 5) ∧
      7 ∈ (Nat.divisors n) ∧ 5 ∈ (Nat.divisors n) := by
  use 5775
  constructor
  · -- Show length of digits is greater than 0
    norm_num
  constructor
  · -- Show all digits are 7 or 5
    intro d hd
    norm_num [Nat.digits, Nat.digitsAux] at hd ⊢
    rcases hd with (rfl | rfl | rfl | rfl)
    all_goals simp
  constructor
  · -- Show that the count of 7s and 5s is equal
    use 4
    constructor
    · -- Show k = length of digits
      norm_num
    · -- Show count 7 = count 5
      native_decide
  constructor
  · -- Show 7 divides 5775
    native_decide
  · -- Show 5 divides 5775
    native_decide
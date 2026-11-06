import Mathlib

theorem number_theory_120226 :
    ∃ n : ℕ, n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ≠ 0 ∧
      101 ∣ n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) := by
  use 1234
  constructor
  · -- Show that 1234 is in the range [1000, 9999]
    native_decide
  constructor
  · -- Show that the length of the digits of 1234 is 4
    native_decide
  constructor
  · -- Show that the cardinality of the digits set is 4
    native_decide
  · -- Show that all digits are non-zero and the divisibility condition holds
    intro d hd
    have h1 : d ∈ (Nat.digits 10 1234) := hd
    have h2 : d = 4 ∨ d = 3 ∨ d = 2 ∨ d = 1 := by
      norm_num [Nat.digits, Nat.digitsAux] at h1 ⊢
      omega
    rcases h2 with (rfl | rfl | rfl | rfl)
    · -- Case d = 4
      constructor
      · norm_num
      all_goals
        native_decide
    · -- Case d = 3
      constructor
      · norm_num
      all_goals
        native_decide
    · -- Case d = 2
      constructor
      · norm_num
      all_goals
        native_decide
    · -- Case d = 1
      constructor
      · norm_num
      all_goals
        native_decide
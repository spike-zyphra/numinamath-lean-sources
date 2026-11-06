import Mathlib

theorem number_theory_146372 :
    ∃ n : ℕ, n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ≠ 0 ∧
      101 ∣ n + (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) := by 
  use 1458
  constructor
  · -- Show that 1458 is in the range [1000, 9999]
    simp [Finset.mem_Icc]
  constructor 
  · -- Show that 1458 has exactly 4 digits
    norm_num
  constructor 
  · -- Show that all digits are distinct
    native_decide
  · -- Show that all digits are non-zero
    intro d hd
    simp [Nat.digits, Nat.digitsAux] at hd ⊢
    rcases hd with (rfl | rfl | rfl | rfl)
    · -- Case where d = 1
      constructor
      · norm_num  -- d ≠ 0
      · norm_num [Nat.ofDigits]
        all_goals omega
    · -- Case where d = 4
      constructor
      · norm_num  -- d ≠ 0
      · norm_num [Nat.ofDigits]
        all_goals omega
    · -- Case where d = 5
      constructor
      · norm_num  -- d ≠ 0
      · norm_num [Nat.ofDigits]
        all_goals omega
    · -- Case where d = 8
      constructor
      · norm_num  -- d ≠ 0
      · norm_num [Nat.ofDigits]
        all_goals omega
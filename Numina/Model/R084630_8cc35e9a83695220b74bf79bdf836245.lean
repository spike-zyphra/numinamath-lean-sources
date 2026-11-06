import Mathlib

theorem number_theory_68186 :
    ∃ n : ℕ, n ∈ Finset.Icc 1000 9999 ∧ (Nat.digits 10 n).length = 4 ∧
      (Nat.digits 10 n).toFinset.card = 4 ∧ ∀ d ∈ (Nat.digits 10 n), d ≠ 0 ∧
      (Nat.ofDigits 10 (List.reverse (Nat.digits 10 n))) + n ≡ 0 [ZMOD 101] := by
  use 1234
  constructor
  · -- Show 1234 ∈ [1000, 9999]
    exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
  constructor
  · -- Show the length of digits in 1234 is 4
    norm_num
  constructor
  · -- Show all digits in 1234 are distinct
    native_decide
  · -- Show that for all digits d in 1234, d ≠ 0 and the sum with reversed number is ≡ 0 [ZMOD 101]
    intro d hd
    have h1 : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 := by
      norm_num [Nat.digits, Nat.digitsAux] at hd ⊢
      omega
    rcases h1 with (rfl | rfl | rfl | rfl)
    · -- d = 1
      constructor
      · norm_num
      · norm_num [Int.ModEq, Nat.ofDigits, Nat.digits, Nat.digitsAux]
    · -- d = 2
      constructor
      · norm_num
      · norm_num [Int.ModEq, Nat.ofDigits, Nat.digits, Nat.digitsAux]
    · -- d = 3
      constructor
      · norm_num
      · norm_num [Int.ModEq, Nat.ofDigits, Nat.digits, Nat.digitsAux]
    · -- d = 4
      constructor
      · norm_num
      · norm_num [Int.ModEq, Nat.ofDigits, Nat.digits, Nat.digitsAux]
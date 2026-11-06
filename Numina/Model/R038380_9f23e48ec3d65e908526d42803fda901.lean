import Mathlib

theorem number_theory_16648 :
    IsLeast {n | n ∈ Set.Icc 16 31 ∧ (Nat.digits 2 n).Palindrome ∧
      ∃ m, m ≠ 2 ∧ (Nat.digits m n).length = 3 ∧  (Nat.digits m n).Palindrome} (2 ^ 4 + 1) := by
  constructor
  · -- Show that 17 is in the set.
    constructor
    · -- Show 17 is in [16, 31]
      norm_num
    constructor
    · -- Show 17 is a palindrome in base 2.
      native_decide
    · -- Show there exists a base m. Let's pick base 4.
      use 4
      constructor
      · -- Show 4 ≠ 2
        norm_num
      constructor
      · -- Show the length is 3.
        native_decide
      · -- Show it's a palindrome.
        native_decide
  · -- Show that 17 is the smallest.
    intro n hn
    rcases hn with ⟨hn1, hn2, ⟨m, hmne2, hmlen, hmpal⟩⟩
    rcases hn1 with ⟨hn1l, hn1u⟩
    by_contra h
    push_neg at h
    have h1 : n = 16 := by
      omega
    rw [h1] at hn2
    norm_num at hn2
    all_goals
      contradiction
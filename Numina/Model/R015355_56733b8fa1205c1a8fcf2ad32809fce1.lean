import Mathlib

theorem number_theory_186549 : ∃ s : Finset ℕ, s.card = 10 ∧ ∀ n ∈ s, n > 0 ∧ ∑ m ∈ s, m ≡ 0 [MOD n] := by
  use {1, 2, 3, 6, 12, 24, 48, 96, 192, 384}
  constructor
  · -- Show that the set has 10 elements.
    native_decide
  · -- Show that all elements in the set are positive and the sum is divisible by each.
    intro n hn
    have h1 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 6 ∨ n = 12 ∨ n = 24 ∨ n = 48 ∨ n = 96 ∨ n = 192 ∨ n = 384 := by
      simp at hn ⊢
      tauto
    rcases h1 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
    · constructor
      · norm_num
      · native_decide
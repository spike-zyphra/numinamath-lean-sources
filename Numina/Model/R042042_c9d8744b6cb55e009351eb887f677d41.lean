import Mathlib

theorem number_theory_610576 :
    IsLeast {n | ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ b = 2 ^ 2023 ∧ n = b ^ a} 1 := by
  constructor
  · -- Show 1 is in the set
    use (2 ^ 2023), 1
    simp
  · -- Show 1 is the smallest
    intro n hn
    rcases hn with ⟨a, b, ha, hb, h1, h2⟩
    have h3 : b ^ a ≥ 1 := by
      apply Nat.one_le_pow
      all_goals linarith
    linarith
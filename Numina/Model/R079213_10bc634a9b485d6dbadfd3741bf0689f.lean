import Mathlib

theorem number_theory_105134 : ¬∃ n, ∃ a b, n^2 = 1234567891011 ∧ a ≠ b ∧ a < 10 ∧ b < 10 ∧ n^2 = 100000000000 + 1000000 * a + 100000 * b + 10000 * 1 + 1000 * 2 + 100 * 3 + 10 * 4 + 1 * 5 := by
  rintro ⟨n, ⟨a, b, hn1, hneq, ha, hb, hn2⟩⟩
  norm_num at hn1 hn2
  all_goals
    omega
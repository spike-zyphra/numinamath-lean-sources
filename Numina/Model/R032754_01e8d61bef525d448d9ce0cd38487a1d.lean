import Mathlib

theorem number_theory_198972 : ∃ k, ∀ n ∈ Finset.Icc k (k + 39), ¬Nat.Prime n ∧ n < 10^9 := by

  use 2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 43

  intro n hn
  rw [Finset.mem_Icc] at hn
  rcases hn with ⟨hn1, hn2⟩
  norm_num at hn1 hn2 ⊢
  interval_cases n <;> norm_num at *
import Mathlib

theorem number_theory_209595 : ∃ m n, Nat.factorial m / Nat.factorial n = 24024 ∧ m = 14 ∧ n = 10 := by
  exact ⟨14, 10, by norm_num [Nat.factorial], by rfl, by rfl⟩
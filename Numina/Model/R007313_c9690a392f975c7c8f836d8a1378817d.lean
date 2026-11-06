import Mathlib

theorem number_theory_607459 : ∃ n, 1000 ∣ Nat.fib n := by
  exact ⟨0, by norm_num [Nat.fib]⟩
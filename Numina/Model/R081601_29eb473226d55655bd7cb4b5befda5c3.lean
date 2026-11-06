import Mathlib

theorem number_theory_7074 (r : ℕ) (hr : r > 0) : ∃ t, r ∣ (Nat.fib t) := by
  exact ⟨0, by simp⟩
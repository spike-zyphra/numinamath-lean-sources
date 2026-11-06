import Mathlib

theorem number_theory_7056 (n : ℕ) :
    ∃ a b c, n = Nat.lcm a b + Nat.lcm b c + Nat.lcm a c ↔ ¬∃ k, n = 2 ^ k := by
  by_cases h : ∃ k, n = 2 ^ k
  · -- Assume that n is a power of 2.
    rcases h with ⟨k, rfl⟩
    use 0, 0, 0
    simp
  · -- Assume that n is not a power of 2.
    push_neg at h
    use n, 1, 0
    simp at *
    all_goals
      tauto
import Mathlib

theorem number_theory_246760 (n : ℕ) :
    ∃ k, Nat.factorial (5 * n) / (40 ^ n * Nat.factorial n) = k := by 
  refine' ⟨Nat.factorial (5 * n) / (40 ^ n * Nat.factorial n), rfl⟩
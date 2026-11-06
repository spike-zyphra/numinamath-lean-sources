import Mathlib

theorem number_theory_83782 {n : ℕ} (hn : ∃ m, m < n ∧ m ∣ n) :
    ∃ k : ℕ, ∃ a : Fin k → ℤ,
      (∀ i, 1 < a i) ∧
      (∑ i, a i) = n * ∑ i, (1 : ℚ) / a i := by
  use 0
  use fun i => 0
  constructor
  · simp
  · simp
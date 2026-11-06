import Mathlib

theorem negated_number_theory_62935 (d : ℕ → ℕ)
    (hd : ∀ n, d n = (Nat.divisors n).card) :
    ∀ N, ∃ (n : ℕ), n > N ∧ ∃ k, (n : ℝ) / d n = k := by
  intro N
  use N + 1
  constructor
  · linarith
  · refine ⟨(N + 1 : ℝ) / d (N + 1), by simp⟩
import Mathlib

theorem number_theory_1694 :
    ∀ N : ℕ, ∃ n : ℕ, n > N ∧ ∃ a b : ℕ, a^2 + b^2 = 2 * n^2 + 2 * n + 1 ∧ |(a : ℤ) - b| = 1 := by
  intro N 
  use (N + 1)
  constructor
  · -- Show that n > N
    simp
  · -- Show existence of a and b
    use (N + 1 + 1), (N + 1)
    constructor
    · -- Show a^2 +b^2 = 2 *n^2 + 2 *n + 1
      ring_nf
    · -- Show |(a : ℤ) - b| = 1
      simp [abs]
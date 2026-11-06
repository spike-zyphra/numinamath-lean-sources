import Mathlib

theorem number_theory_255317 (n : ℕ) :
    ∃ a : ℕ → ℕ,
      (∀ i ∈ Finset.range (2 * n + 1), a i > 0) ∧
      (∃ d, ∀ i ∈ Finset.range (2 * n), a (i + 1) = a i + d) ∧
      (∃ m, m^2 = ∏ i ∈ Finset.range (2 * n + 1), a i) := by
  use (λ _ => (1 : ℕ))
  constructor
  · -- Show all terms are positive
    intro i hi
    simp
  constructor
  · -- Show that it is an arithmetic sequence.
    use (0 : ℕ)
    intro i hi
    all_goals simp
  · -- Show that the product is a square.
    use (1 : ℕ)
    rw [Finset.prod_const]
    simp
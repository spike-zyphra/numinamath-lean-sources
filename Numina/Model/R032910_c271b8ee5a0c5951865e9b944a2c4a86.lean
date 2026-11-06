import Mathlib

theorem number_theory_152921 (a : Fin 10 → ℤ) :
    ∃ ε : Fin 10 → ℤ,
      (∀ i, ε i = 0 ∨ ε i = 1 ∨ ε i = -1) ∧
      1001 ∣ ∑ i, ε i * a i := by
  use (λ _ => 0)
  constructor
  · -- Show that for all i, ε i = 0 ∨ ε i = 1 ∨ ε i = -1
    intro i
    simp
  · -- Show that 1001 divides the sum
    simp [Finset.sum_eq_zero]
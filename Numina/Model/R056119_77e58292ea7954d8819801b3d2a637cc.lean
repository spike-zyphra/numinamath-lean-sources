import Mathlib

theorem number_theory_182668 (a : Fin 5 → ℕ) (ha : ∀ i, a i > 0)
    (h : ∏ i, (a i - 3) = 15 * ∏ i, a i) :
    ∃ x, x = 720 := by
  exact ⟨720, rfl⟩
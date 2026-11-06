import Mathlib

theorem number_theory_179872 (a : Fin 10 → ℕ) (ha : ∀ i j, a i % 10 ≠ a j % 10) :
    ¬∃ b : Fin 10 → ℕ, (∀ i j, b i % 10 ≠ b j % 10) ∧
      (∑ i, b i) = 2 * ∑ i, a i := by 
  have h : False := by
    specialize ha 0 0
    simpa using ha 
  exact False.elim h
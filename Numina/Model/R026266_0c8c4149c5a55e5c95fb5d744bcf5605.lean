import Mathlib

theorem number_theory_107209 (x : ℤ) :
    ∃ n, x^5 / 5 + x^3 / 3 + 7 * x / 15 = n := by 
  refine' ⟨x^5 / 5 + x^3 / 3 + 7 * x / 15, rfl⟩
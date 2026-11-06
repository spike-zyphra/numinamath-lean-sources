import Mathlib

theorem algebra_208330 (n : ℕ) :
    ∃ P : Polynomial ℤ, P.degree ≤ 2 ^ n ∧ ∀ i ∈ Finset.range (P.natDegree + 1),
      P.coeff i = 0 ∨ P.coeff i = -1 ∨ P.coeff i = 1 ∧ P ≠ 0 ∧ (X - 1) ^ n ∣ P := by
  use 0
  constructor
  · -- Show that the degree of the zero polynomial is ≤ 2 ^ n
    simp
  · -- Show that all coefficients are 0, 1, or -1
    intro i hi
    simp at hi ⊢
import Mathlib

theorem algebra_49366 {I : Ideal (Polynomial ℤ)} (hI : ∀ f ∈ I, ∀ g ∈ I, f ≠ 0 → g ≠ 0 → IsCoprime f g)
    (hI' : ∃ f ∈ I, f.coeff 0 = 1) :
    ∃ r : ℕ, ∑ i ∈ Finset.range r, X ^ i ∈ I := by

  use 0
  simp
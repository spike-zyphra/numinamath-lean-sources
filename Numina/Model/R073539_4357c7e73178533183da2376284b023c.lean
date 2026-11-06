import Mathlib

theorem number_theory_3597 {x y z w : ℤ} (h : ∃ d : ℤ, y^2 = x^2 + d ∧ z^2 = y^2 + d ∧ w^2 = z^2 + d) :
    x^2 + z^2 = 2 * y^2 ∧ y^2 + w^2 = 2 * z^2 := by 
  rcases h with ⟨d, h1, h2, h3⟩
  constructor
  · -- Proof of $x^2 + z^2 = 2 * y^2$
    linarith [h1, h2]
  · -- Proof of $y^2 + w^2 = 2 * z^2$
    linarith [h2, h3]
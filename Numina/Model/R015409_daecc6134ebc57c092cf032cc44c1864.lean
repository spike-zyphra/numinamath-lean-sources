import Mathlib

theorem number_theory_222700 (a b c : ℤ) (_ : 0 < a) (h₀ : 0 < b) (h₁ : 0 < c)
    (h₂ : ∃ q : ℚ, (a * Real.sqrt 2013 + b) / (b * Real.sqrt 2013 + c) = q) :
    ∃ m n : ℤ, (a^2 + b^2 + c^2) / (a + b + c) = m ∧
    (a^3 - 2 * b^3 + c^3) / (a + b + c) = n := by

  refine' ⟨(a^2 + b^2 + c^2) / (a + b + c), (a^3 - 2 * b^3 + c^3) / (a + b + c), rfl, rfl⟩
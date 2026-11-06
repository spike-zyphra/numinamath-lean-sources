import Mathlib

theorem number_theory_154108 (v d : ℕ) (h₀ : v > 0) (h₁ : d > 0)
    (h₂ : v * 5 + d * 3 = 2018) :
    v + d ≠ 673 := by
  intro H
  omega
import Mathlib

theorem number_theory_6663 (d : ℤ) (x₁ x₂ y₁ y₂ : ℤ) :
    ∃ x y, (x₁^2 - d * y₁^2) * (x₂^2 - d * y₂^2) = x^2 - d * y^2 := by
  use x₁ * x₂ + d * (y₁ * y₂)
  use x₁ * y₂ + x₂ * y₁
  ring_nf
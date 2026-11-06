import Mathlib

theorem algebra_119658 (d : ℝ) (h₀ : d > 0) (v₁ v₂ v₃ : ℝ)
    (h₁ : v₁ = 4) (h₂ : v₂ = 2) (h₃ : v₃ = 3) :
    (d / 2) / (d / 2 / v₁ + d / 2 / v₂ + d / 2 / v₃) = 12 / 13 := by
  rw [h₁, h₂, h₃]
  field_simp
  <;> ring_nf
  <;> nlinarith
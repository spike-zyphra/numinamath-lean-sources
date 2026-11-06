import Mathlib

theorem algebra_241508 (d : ℝ) (h₀ : d > 0) (v₁ v₂ v₃ : ℝ)
    (h₁ : v₁ > 0) (h₂ : v₂ > 0) (h₃ : v₃ > 0)
    (h₄ : v₁ / v₂ = 1 / 5) (h₅ : d * (20 / 81) = v₁ * t₁ + v₂ * t₂)
    (h₆ : d * (56 / 81) = v₁ * t₃ + v₂ * t₄) :
    d * (56 / 81) / d = 56 / 81 := by
  have h7 : d ≠ 0 := by linarith
  field_simp [h7]
  <;> nlinarith
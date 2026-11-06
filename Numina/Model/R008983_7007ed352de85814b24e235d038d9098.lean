import Mathlib

theorem algebra_12480 (v₁ v₂ : ℝ) (h₁ : v₁ * 20 = 1) (h₂ : v₂ * 30 = 1) :
    (3 / (v₁ + v₂)) = 36 := by
  have hv₁ : v₁ = 1 / 20 := by
    linarith
  have hv₂ : v₂ = 1 / 30 := by
    linarith
  rw [hv₁, hv₂]
  norm_num
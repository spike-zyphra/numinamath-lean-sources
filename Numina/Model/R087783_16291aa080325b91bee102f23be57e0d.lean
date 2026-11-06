import Mathlib

theorem algebra_320745 (d : ℝ) (h₀ : d > 0) (v₁ v₂ v₃ : ℝ)
    (h₁ : v₁ > 0) (h₂ : v₂ > 0) (h₃ : v₃ > 0) :
    (3 * d) / (d / v₁ + d / v₂ + d / v₃) = 3 / (1 / v₁ + 1 / v₂ + 1 / v₃) := by
  have h4 : d / v₁ + d / v₂ + d / v₃ = d * (1 / v₁ + 1 / v₂ + 1 / v₃) := by
    field_simp [h₁.ne.symm, h₂.ne.symm, h₃.ne.symm]
    <;> ring
  rw [h4]
  field_simp [(show d ≠ 0 by linarith), (show (1 / v₁ + 1 / v₂ + 1 / v₃) ≠ 0 by
    positivity
  )]
  <;> ring
  <;> field_simp [(show d ≠ 0 by linarith), (show (1 / v₁ + 1 / v₂ + 1 / v₃) ≠ 0 by
    positivity
  )]
  <;> ring
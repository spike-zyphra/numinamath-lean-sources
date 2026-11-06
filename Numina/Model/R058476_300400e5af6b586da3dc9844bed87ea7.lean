import Mathlib

theorem algebra_105867 (d : ℝ) (h₀ : d > 0) (v₁ v₂ : ℝ)
    (h₁ : v₁ = 30) (h₂ : v₂ = 60) :
    (2 * d) / (d / v₁ + d / v₂) = 40 := by
  rw [h₁, h₂]
  have h3 : d / (30 : ℝ) + d / (60 : ℝ) = d / (20 : ℝ) := by
    linarith
    -- field_simp
    -- ring_nf
  rw [h3]
  field_simp [show d ≠ 0 by linarith]
  <;> ring_nf <;> field_simp [show d ≠ 0 by linarith]
  <;> linarith
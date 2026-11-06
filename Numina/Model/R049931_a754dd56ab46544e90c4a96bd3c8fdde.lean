import Mathlib

theorem algebra_230400 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / 50 = d / v + 1) (h₃ : d / 50 - d / v = 20) :
    d = 110 ∧ v = 60 := by 
  have eq1 : d / 50 - d / v = 1 := by 
    field_simp [(show v ≠ 0 by linarith)] at h₂ ⊢
    linarith
  linarith -- This will detect the contradiction between eq1 and h₃.
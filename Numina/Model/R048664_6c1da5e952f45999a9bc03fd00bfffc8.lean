import Mathlib

theorem algebra_224133 (d v : ℝ) (h₀ : d > 0) (h₁ : v > 0)
    (h₂ : d / (2.5 * v) = d / v + 30 / 60) :
    d / v = 330 := by
  field_simp [(show 2.5 * v ≠ 0 by nlinarith), (show v ≠ 0 by linarith)] at h₂ ⊢
  nlinarith
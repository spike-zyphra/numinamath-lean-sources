import Mathlib

theorem algebra_154244 (h m f : ℝ)
    (h₀ : 3 * h + 5 * m + f = 23.50)
    (h₁ : 5 * h + 9 * m + f = 39.50) :
    2 * h + 2 * m + 2 * f = 15 := by
  ring_nf at h₀ h₁ ⊢
  linarith
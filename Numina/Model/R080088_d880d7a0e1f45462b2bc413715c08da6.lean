import Mathlib

theorem algebra_136176 (v d : ℝ) (h₀ : v > 0) (h₁ : d > 0)
    (h₂ : 420 * v + 80 * d = 11) (h₃ : 240 * v + 140 * d = 11) :
    198 * v = 3.3 := by 
  ring_nf at h₂ h₃ ⊢ 
  linarith
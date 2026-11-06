import Mathlib

theorem algebra_186962 (d p c : ℝ) (h₀ : d > 0) (h₁ : p > 0) (h₂ : c > 0)
    (h₃ : p * 1 = c * 1.5) (h₄ : p * 1.5 = c * 2) :
    d / p = 5 := by 
  ring_nf at h₃ h₄ 
  -- h₃ and h₄ lead to a contradiction since c > 0
  nlinarith -- contradictory equations
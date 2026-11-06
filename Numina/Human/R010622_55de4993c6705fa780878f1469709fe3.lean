import Mathlib

theorem algebra_158081 (v₁ v₂ t: ℝ) (hv : 0 < v₁)
    (h₀ : (6 + 12) * v₂ = 12 * v₁) 
    (h₁ : (6 + t) * v₂ = t * 2 * v₁) :
    t = 3 := by
  have : 6 + t = t * 3 := by 
    have : v₁ = 3/2 * v₂ := by linarith
    rw [this] at h₁
    apply mul_right_cancel₀ (show v₂ ≠ 0 by linarith)
    linarith
  linarith

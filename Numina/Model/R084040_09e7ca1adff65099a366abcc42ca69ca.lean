import Mathlib

theorem algebra_270333 (v c : ℝ) (h₀ : v > 0) (h₁ : c > 0)
    (h₂ : c = 30 / v) (h₃ : c + 10 / v = 50 / v) :
    c / v = 8 := by
  rw [h₂] at h₃
  field_simp [show v ≠ 0 by linarith] at h₃
  all_goals linarith
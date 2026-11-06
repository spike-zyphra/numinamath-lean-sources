import Mathlib

theorem algebra_11320 (a r : ℚ) (h₀ : a = 16) (h₁ : r ≠ 0)
    (h₂ : a * r = -24) (h₃ : -24 * r = 36) (h₄ : 36 * r = -54) :
    r = -3 / 2 := by
  rw [h₀] at h₂ -- rewrite a as 16 in h₂
  linarith -- solves linear equations
import Mathlib

theorem algebra_298538 (a d : ℤ) (h₀ : a = 55) (h₁ : d ≠ 0)
    (h₂ : a + 6 * d = 555) :
    d = 4 := by
  rw [h₀] at h₂
  omega
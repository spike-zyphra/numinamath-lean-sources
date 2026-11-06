import Mathlib

theorem algebra_93894 (a b c d e : ℕ) (h₀ : a ≤ 100) (h₁ : b ≤ 100)
    (h₂ : c ≤ 100) (h₃ : d ≤ 100) (h₄ : e ≤ 100) (h₅ : (a + b + c + d + e) / 5 = 81)
    (h₆ : a = 76) (h₇ : b = 94) (h₈ : c = 87) :
    min d e ≥ 48 := by
  -- Substitute the given values into the equation
  norm_num [h₆, h₇, h₈] at h₅
  -- Let omega solve the arithmetic constraints.
  omega
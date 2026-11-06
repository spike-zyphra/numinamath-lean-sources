import Mathlib

theorem algebra_19572 (a b c d : ℤ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (h₀ : a + b + d = 14 * c) (h₁ : a + b = 6 * c)
    (h₂ : b = d - a - 2) : c = 1 := by
  have h3 : d = 8 * c := by 
    linarith
  rw [show d = 8 * c by linarith [h3]] at h₂
  linarith [h₁, h₂]
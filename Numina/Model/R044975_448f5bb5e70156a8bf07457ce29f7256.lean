import Mathlib

open scoped BigOperators

theorem inequalities_35365
  (f : ℚ → ℚ)
  (h₀ : ∀ x y, 0 < x → 0 < y → f x + f y ≥ 4 * f (x + y))
  (x y z : ℚ)
  (hx : 0 < x)
  (hy : 0 < y)
  (hz : 0 < z) :
  f x + f y + f z ≥ 8 * f (x + y + z) := by
  have h7 : f x + f y + 4 * f z ≥ 16 * f (x + y + z) := by
    have h1 := h₀ x y hx hy
    have h2 := h₀ (x + y) z (by positivity) hz
    ring_nf at h1 h2 ⊢
    linarith
  have h8 : 4 * f x + f y + f z ≥ 16 * f (x + y + z) := by
    have h3 := h₀ x (y + z) hx (by positivity)
    have h4 := h₀ y z hy hz
    ring_nf at h3 h4 ⊢
    linarith
  have h9 : f x + 4 * f y + f z ≥ 16 * f (x + y + z) := by
    have h5 := h₀ x z hx hz
    have h6 := h₀ y (x + z) hy (by positivity)
    ring_nf at h5 h6 ⊢
    linarith
  linarith
import Mathlib

theorem algebra_243883 (f : ℝ → ℝ) (h : ∀ x y, f (2 * x - 3 * y) - f (x + y) = -2 * x + 8 * y) :
    ∀ t, f (5 * t) - f t = 4 * (f (4 * t) - f (3 * t)) := by
  intro t
  have eq1 := h (8 * t / 5) (-3 * t / 5)
  have eq2 := h (13 * t / 5) (2 * t / 5)
  have eq3 : f (5 * t) - f t = -8 * t := by
    have h1 := eq1
    ring_nf at h1 ⊢
    linarith
  have eq4 : f (4 * t) - f (3 * t) = -2 * t := by
    have h2 := eq2
    ring_nf at h2 ⊢
    linarith
  linarith [eq3, eq4]
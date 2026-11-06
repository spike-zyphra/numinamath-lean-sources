import Mathlib

theorem algebra_13906 {a b c : ℤ} (ha : a ≠ 0) (h : ∀ x, 9 * x ^ 2 - 30 * x - 42 = (a * x + b) ^ 2 + c) :
    a * b = -15 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  ring_nf at h0 h1 h2 h3
  have h4 : a^2 + 2 * a * b = -21 := by
    nlinarith
  have h5 : 3 * a^2 + 2 * a * b = -3 := by
    nlinarith
  have h6 : a^2 = 9 := by
    nlinarith
  nlinarith
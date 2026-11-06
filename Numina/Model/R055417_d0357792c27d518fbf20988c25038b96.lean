import Mathlib

theorem algebra_14558 (a b : ℝ) (ha : a > 0) (hb : b > 0)
    (h1 : ∀ x, (x + 1) ^ 2 - a * x ^ 2 = b ^ 2) (h2 : ∀ x, (3 - x) ^ 2 - a * x ^ 2 = b ^ 2)
    (h3 : a * 3 ^ 2 - b ^ 2 = 0) :
    2 * Real.sqrt (a ^ 2 + b ^ 2) = 2 * Real.sqrt 6 := by
    have h4 := h1 0
    have h5 := h2 0
    nlinarith
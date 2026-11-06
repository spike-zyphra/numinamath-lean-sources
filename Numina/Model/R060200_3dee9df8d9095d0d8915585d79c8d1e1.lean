import Mathlib

theorem algebra_10427 {x : ℝ} (hx : x > 0) (h : x + x^2 = 156) : x = 12 := by
  have h1 : x^2 + x - 156 = 0 := by
    linarith
  have h2 : (x - 12) * (x + 13) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Solving $x - 12 = 0$ gives $x = 12$
    linarith
  · -- Solving $x + 13 = 0$ gives $x = -13$, but we need $x > 0$, contradiction
    linarith -- with hx: x > 0
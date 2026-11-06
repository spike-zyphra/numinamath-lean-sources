import Mathlib

theorem algebra_269136 (x : ℝ) (hx : x > 0) (h : (1 / 5) * x * (1 / 7) = x) : x = 35 := by
  have h1 : x ^ 2 = 35 * x := by
    nlinarith
  have h2 : x * (x - 35) = 0 := by
    linarith [h1]
  cases' (mul_eq_zero.1 h2) with h3 h4
  · -- case where $x = 0$, but $x > 0$ contradicts
    linarith
  · -- so $x - 35 = 0$, or $x = 35$
    linarith
import Mathlib

theorem algebra_288545 (a : ℝ) (ha : a ≠ 0) (h : a^2 = 5 * a + a) : a = 6 := by
  have h1 : a^2 = 6 * a := by
    linarith
  have h2 : a^2 - 6 * a = 0 := by
    linarith
  have h3 : a * (a - 6) = 0 := by
    linarith [h2]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $a = 0$, which contradicts $a \neq 0$
    exfalso
    exact ha h4
  · -- Case $a - 6 = 0$, so $a = 6$
    linarith
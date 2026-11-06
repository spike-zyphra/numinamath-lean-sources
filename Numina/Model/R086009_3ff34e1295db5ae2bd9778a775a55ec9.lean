import Mathlib

theorem algebra_3231
  {a b : ℝ}
  (h : a^2 - 2*a - 19 = 0 ∧ b^2 - 2*b - 19 = 0)
  (hab : a ≠ b) :
  a^2 + 2*b = 23 := by
  have ha : a^2 - 2 * a - 19 = 0 := h.1
  have hb : b^2 - 2 * b - 19 = 0 := h.2
  have h_diff : (a - b) * (a + b - 2) = 0 := by
    have eq1 : a^2 - 2 * a - 19 = 0 := ha
    have eq2 : b^2 - 2 * b - 19 = 0 := hb
    nlinarith
  cases' (mul_eq_zero.mp h_diff) with h1 h2
  · -- Case where $a - b = 0$, so $a = b$
    exfalso
    exact hab (by linarith)
  · -- Case where $a + b - 2 = 0$, so $a + b = 2$
    have hab2 : a + b = 2 := by linarith
    have ha2 : a^2 = 2 * a + 19 := by linarith
    linarith [ha2, hab2]
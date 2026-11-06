import Mathlib

theorem algebra_324808 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h1 : a + b^2 + 2 * a * c = 29) (h2 : b + c^2 + 2 * a * b = 18)
    (h3 : c + a^2 + 2 * b * c = 25) : a + b + c = 8 := by
  have h4 : (a + b + c)^2 + (a + b + c) - 72 = 0 := by
    nlinarith
  have h6 : (a + b + c + 9) * (a + b + c - 8) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h6) with h7 h8
  · -- Case where $a + b + c + 9 = 0$, which is impossible since $a$, $b$, $c$ are positive
    nlinarith
  · -- Case where $a + b + c - 8 = 0$, which gives the correct value
    nlinarith
import Mathlib

theorem algebra_116982 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h1 : 1 / (a + b) = 1 / 30) (h2 : 10 * (a + b) + 40 * b = 1) :
    1 / b = 60 := by
  have h3 : a + b = 30 := by
    field_simp [(show a + b ≠ 0 by nlinarith)] at h1
    linarith
  rw [h3] at h2
  -- After the substitution, we get $10 * 30 + 40 * b = 1$, which simplifies to $300 + 40 * b = 1$.
  -- This would mean $40 * b = -299$, and $b < 0$, which contradicts $hb : 0 < b$.
  -- Therefore, Lean's `nlinarith` would detect the contradiction.
  field_simp [(show b ≠ 0 by nlinarith)] at *
  nlinarith -- After contradiction, any goal can be proven
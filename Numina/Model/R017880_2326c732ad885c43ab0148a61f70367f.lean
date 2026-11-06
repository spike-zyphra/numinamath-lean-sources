import Mathlib

theorem number_theory_68303
    (a b : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (h : (2 * a + b) * (2 * b + a) = 4752) :
    a * b = 520 := by

  have h1 : a ≤ 48 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (2 * a + b - (2 * b + a)), h, mul_pos ha hb]

  have h2 : b ≤ 48 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (2 * a + b - (2 * b + a)), h, mul_pos ha hb]

  interval_cases a <;> interval_cases b
  <;> omega
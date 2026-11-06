import Mathlib

theorem number_theory_304358 (a b : ℤ) (ha : a > 0) (hb : b > 0)
    (h : a^2 + a * b + b^2 = 2010) :
    False := by
  have h1 : a ≤ 44 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h2 : b ≤ 44 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  interval_cases a <;> interval_cases b
    <;> omega
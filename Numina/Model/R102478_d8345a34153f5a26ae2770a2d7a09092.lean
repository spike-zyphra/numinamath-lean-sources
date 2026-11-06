import Mathlib

theorem algebra_309102
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h : a^2 + b^2 + c^2 - a * b - b * c - c * a = 19) :
    a + b + c ≥ 10 := by 
  by_contra h1
  push_neg at h1
  have h2 : a ≤ 7 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h1]
  have h3 : b ≤ 7 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h1]
  have h4 : c ≤ 7 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a), h1]
  interval_cases a <;> interval_cases b <;> interval_cases c
  <;> omega
import Mathlib

theorem algebra_98677 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hle : a ≤ b) (hsum : a^2 + b^2 + 8 * a * b = 2010) :
    a + b = 42 := by
  have h1 : a ≤ 44 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h2 : b ≤ 44 := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  interval_cases a <;> interval_cases b 
    <;> omega
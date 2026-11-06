import Mathlib

theorem algebra_9644 {a b : ℝ} (ha : a^2+b^2=74) (hb : a^3+b^3=218) :
    a^4+b^4=3026 := by
  have h1 : a + b = 2 := by
    have eq2 : a^2 + b^2 = 74 := ha
    have eq3 : a^3 + b^3 = 218 := hb
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b - 2), sq_nonneg (a - 7), sq_nonneg (a + 5), sq_nonneg (b - 7), sq_nonneg (b + 5)]
  have h2 : a * b = -35 := by
    nlinarith [sq_nonneg (a - b), h1]
  nlinarith [sq_nonneg (a^2 - b^2), sq_nonneg (a * b), h2, ha]
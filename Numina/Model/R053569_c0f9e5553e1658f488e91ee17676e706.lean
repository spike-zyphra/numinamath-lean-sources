import Mathlib

theorem algebra_6931 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : a ^ 2 + b ^ 2 = 2) :
    (a + b + 2) * (a + b + 2 * a * b) / ((a + 1) * (b + 1)) ≤ 4 := by
  have h1 : 0 < (a + 1) * (b + 1) := by
    apply mul_pos
    linarith
    linarith
  have h2 : (a + b + 2) * (a + b + 2 * a * b) ≤ 4 * ((a + 1) * (b + 1)) := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - 1), sq_nonneg (b - 1),
      sq_nonneg (a + b - 2), sq_nonneg (a * b - 1),
      sq_nonneg (a - b), h, mul_pos ha hb]
  apply (div_le_iff₀ h1).mpr
  linarith
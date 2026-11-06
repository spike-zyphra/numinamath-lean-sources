import Mathlib

theorem inequalities_597970 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * (a ^ 3 + b ^ 3) ≥ (a + b) ^ 3 ∧
    9 * (a ^ 3 + b ^ 3 + c ^ 3) ≥ (a + b + c) ^ 3 := by
  constructor
  · -- First inequality $4(a^3 + b^3) \geq (a+b)^3$.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b), mul_pos ha hb, sq_nonneg (a^2 - b^2)]
  · -- Second inequality $9(a^3 + b^3 + c^3) \geq (a + b + c)^3$.
    nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c), sq_nonneg (a + b + c), 
              mul_pos ha hb, mul_pos hb hc, mul_pos ha hc, sq_nonneg (a * b - b * c), sq_nonneg (b * c - c * a), sq_nonneg (c * a - a * b)]
import Mathlib

theorem inequalities_291510 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    4 * (a ^ 3 + b ^ 3 + c ^ 3 + 3) ≥ 3 * (a + 1) * (b + 1) * (c + 1) := by
  --Simplify the expression and notice it can be re-arranged to the desired form 
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c),
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
    mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
    sq_nonneg (a + b + c - (a * b + a * c + b * c)), sq_nonneg (a * b * c)]
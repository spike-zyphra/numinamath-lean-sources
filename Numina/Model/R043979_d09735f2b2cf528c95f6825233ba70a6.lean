import Mathlib

theorem inequalities_638 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : a + b + c = 6) :
    (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≤ 27 ∨ a * b ^ 2 + b * c ^ 2 + c * a ^ 2 ≤ 27) := by 
  by_cases h1 : a ^ 2 * b + b ^ 2 * c + c ^ 2 * a ≤ 27
  · -- First expression is ≤ 27.
    left
    linarith
  · -- Assume the first expression > 27, need to show second expression ≤ 27
    right
    nlinarith [sq_nonneg (a - 3), sq_nonneg (b - 3), sq_nonneg (c - 3), 
              sq_nonneg (a * b - 9), sq_nonneg (b * c - 9), sq_nonneg (c * a - 9), 
              h, mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg ha hc]
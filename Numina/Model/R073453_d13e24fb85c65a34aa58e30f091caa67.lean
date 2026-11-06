import Mathlib

theorem inequalities_82402  (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h1 : a ≤ 2 * b) (h2 : 2 * b ≤ 4 * a) : 4 * a * b ≤ 2 * (a ^ 2 + b ^ 2) ∧ 2 * (a ^ 2 + b ^ 2) ≤ 5 * a * b := by 
  constructor
  · -- We need to show that $4ab \leq 2(a^2 + b^2)$, which simplifies to $0 \leq (a-b)^2$
    nlinarith [sq_nonneg (a - b)]
  · -- For the second inequality $2(a^2 + b^2) \leq 5ab$
    nlinarith [sq_nonneg (a - 2 * b), sq_nonneg (a - b / 2), mul_pos ha hb]
import Mathlib

open Real
open scoped BigOperators

theorem inequalities_84913 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) :
  2 * (a^3 + b^3 + c^3) < (a + b + c) * (a^2 + b^2 + c^2) ∧
  (a + b + c) * (a^2 + b^2 + c^2) ≤ 3 * (a^3 + b^3 + c^3) := by
  constructor
  · -- Prove the first inequality: $2(a^3 + b^3 + c^3) < (a + b + c)(a^2 + b^2 + c^2)$
    nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc,
            sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
  · -- Prove the second inequality: $(a + b + c)(a^2 + b^2 + c^2) \le 3(a^3 + b^3 + c^3)$
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
            sq_nonneg (a + b - c), sq_nonneg (b + c - a), sq_nonneg (c + a - b),
            mul_pos ha hb, mul_pos hb hc, mul_pos ha hc
            ]
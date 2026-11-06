import Mathlib

open Real
open scoped BigOperators

theorem inequalities_157076 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a^2 + b^2 + c^2) ≥ (1 / 2) * (2 * (a * b + b * c + a * c)) := by 
        nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
                  sq_nonneg (a + b + c), sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
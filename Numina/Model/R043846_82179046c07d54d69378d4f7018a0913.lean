import Mathlib

open Real
open scoped BigOperators

theorem inequalities_598567 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a^2 * b * (a - b) + b^2 * c * (b - c) + c^2 * a * (c - a) ≥ 0 := by

  have h1 : a + b - c > 0 := by linarith
  have h2 : a + c - b > 0 := by linarith
  have h3 : b + c - a > 0 := by linarith
  have h4 : 0 < a * b * c := by
    apply mul_pos
    apply mul_pos
    exact ha
    exact hb
    exact hc

  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a * (a - b)), sq_nonneg (b * (b - c)), sq_nonneg (c * (c - a)),
          mul_pos ha hb, mul_pos ha hc, mul_pos hb hc,
          mul_pos (show 0 < a + b - c by linarith) (show 0 < a + c - b by linarith),
          mul_pos (show 0 < a + c - b by linarith) (show 0 < b + c - a by linarith),
          mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith)
        ]
import Mathlib

open Real
open scoped BigOperators

theorem inequalities_92125 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : b + c > a) (h'' : c + a > b) (h''' : a + b + c = 2) :
  a * b * c + 1 / 27 ≥ a * b + b * c + c * a - 1 ∧
  a * b + b * c + c * a - 1 ≥ a * b * c := by
  constructor
  · -- First inequality: `a * b * c + 1 / 27 ≥ a * b + b * c + c * a - 1`
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
      mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
      mul_pos (show 0 < a + b - c by linarith) (show 0 < c + a - b by linarith)
      ]
  · -- Second inequality: `a * b + b * c + c * a - 1 ≥ a * b * c`
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
      mul_pos ha hb, mul_pos hb hc, mul_pos ha hc,
      mul_pos (show 0 < a + b - c by linarith) (show 0 < b + c - a by linarith),
      mul_pos (show 0 < b + c - a by linarith) (show 0 < c + a - b by linarith),
      mul_pos (show 0 < a + b - c by linarith) (show 0 < c + a - b by linarith)
      ]
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Tactic

theorem inequalities_140167 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
  (h : a * b * c ≤ a + b + c) : a * a + b * b + c * c ≥ a * b * c := by
    nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
          sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
          mul_nonneg ha hb, mul_nonneg ha hc, mul_nonneg hb hc
      ]
import Mathlib

theorem algebra_217022 {S T r : ℝ} (hS : S > 0) (hT : T > 0) (hr : r > 0)
    (h : S - 2 * T + r * S - 0.5 * r * T + (0.5 * r * S) ^ 2 < S - 2 * T + r * S) :
    True := by
  trivial
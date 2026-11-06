import Mathlib

theorem algebra_222002 {a b c : ℝ} (ha : a ≠ 0) (h : ∀ x, a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + b * x + a = 0 → x ≠ 0 ∧ (x + 1 / x) ^ 2 - 4 * a * (x + 1 / x) + 4 * b * (x + 1 / x) + 2 * c = 0 ∨ (x + 1 / x) ^ 2 - 4 * b * (x + 1 / x) + 4 * c * (x + 1 / x) + 2 * a = 0) :
    True := by
  trivial
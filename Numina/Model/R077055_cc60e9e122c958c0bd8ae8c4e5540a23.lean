import Mathlib

theorem algebra_244341 {a b : ℝ} (ha : a ≠ 0) (h : ∀ x y, a * x ^ 3 + b * x ^ 2 * y + b * x * y ^ 2 + a * y ^ 3 = 0 → x / y = 1 / 2) :
    True := by
  trivial
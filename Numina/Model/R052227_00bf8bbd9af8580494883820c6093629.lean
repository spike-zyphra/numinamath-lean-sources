import Mathlib

theorem algebra_177388 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : 1.6 * ((1 / a + 1 / b - 2 * c / (a * b)) * (a + b + 2 * c)) /
      ((1 / a ^ 2) + (1 / b ^ 2) + (2 / (a * b)) - (4 * c ^ 2 / (a ^ 2 * b ^ 2))) = 1) :
    True := by 
  trivial
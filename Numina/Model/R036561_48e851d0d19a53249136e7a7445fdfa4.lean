import Mathlib

theorem algebra_22108 {a b c : ℝ} (ha : a ≠ 0) (h0 : 5 = a * 0 ^ 2 + b * 0 + c)
    (h1 : 10 = a * 1 ^ 2 + b * 1 + c) (h2 : 19 = a * 2 ^ 2 + b * 2 + c) :
    a + b + c = 10 := by
  linarith
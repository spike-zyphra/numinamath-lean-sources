import Mathlib

theorem inequalities_202048 {a b c : ℝ} (h : a * b + b * c + c * a = 1) :
    (a + b + c)^2 ≥ 3 := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a)]
import Mathlib

theorem algebra_185041 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∃ x, x = a ^ ((2 : ℝ) / 3) * b ^ ((-1 : ℝ) / 2) ∧
      (x ^ 3 - a ^ ((-2 : ℝ) / 3) * b ^ ((-1 : ℝ)) * (a ^ 2 + b ^ 2) * x +
       b ^ ((1 : ℝ) / 2)) / (b ^ ((3 : ℝ) / 2) * x ^ 2) = 0) :
    True := by 
  trivial
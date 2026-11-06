import Mathlib

theorem algebra_258698 (a b c d : ℝ)
    (ha : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d)
    (h1 : a * 9 = b * 8 + c * 8)
    (h2 : a * 10 = d * 8 + b * 8 + c * 8)
    (h3 : d * 12 = b * 10 + c * 10)
    (h4 : d * 2 = b * 14 + c * 14) :
    b * 10 = c * 12 := by 
  linarith
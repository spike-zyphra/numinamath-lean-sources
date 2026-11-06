import Mathlib

theorem algebra_143074 {b1 b2 b3 c1 c2 c3 : ℝ} (h : b1^2 - 4 * c1 = 1) (h' : b2^2 - 4 * c2 = 4)
    (h'' : b3^2 - 4 * c3 = 9) :
    ∃ x1 x2 x3, x1^2 + b1 * x1 + c1 = 0 ∧ x2^2 + b2 * x2 + c2 = 0 ∧ x3^2 + b3 * x3 + c3 = 0 ∧
    x1 + x2 + x3 = - (b1 + b2 + b3) / 2 := by 
  use (-b1 - 1) / 2, (-b2 - 2) / 2, (-b3 + 3) / 2
  constructor
  · -- Show that (-b1 - 1) / 2 is a root of the first equation.
    nlinarith [h]
  constructor
  · -- Show that (-b2 - 2) / 2 is a root of the second equation.
    nlinarith [h']
  constructor
  · -- Show that (-b3 + 3) / 2 is a root of the third equation.
    nlinarith [h'']
  · -- Show that the sum of the chosen roots is equal to the required sum.
    linarith
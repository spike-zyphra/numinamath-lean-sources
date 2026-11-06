import Mathlib

theorem algebra_221149 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a = (b + c) / 2) (h2 : b = (a + c) / 3) (h3 : c = (a + b) / 4)
    (h4 : a + b + c = 12) :
    a = 3 + 9 / 17 ∧ b = 7 + 13 / 17 ∧ c = 9 + 3 / 17 := by
  constructor
  · -- Solving the system of equations to find a
    linarith
  constructor
  · -- Solving the system of equations to find b
    linarith
  · -- Solving the system of equations to find c
    linarith
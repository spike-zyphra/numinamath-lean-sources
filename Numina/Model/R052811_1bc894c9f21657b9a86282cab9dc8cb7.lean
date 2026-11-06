import Mathlib

theorem algebra_103670 (a b : ℤ) (ha : a > 0) (hb : b > 0)
    (h : a * b = 21) (h' : a ^ 3 + b ^ 3 = 8) :
    ¬(a * b = 2013201420152016) := by
  intro H
  omega
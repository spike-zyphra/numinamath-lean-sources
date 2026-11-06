import Mathlib

theorem inequalities_176734 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (h1 : a / 2 + b / 2 = c) (h2 : c < a / 3) :
    a / 2 > b / 2 := by
  omega
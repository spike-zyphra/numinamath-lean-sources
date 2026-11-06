import Mathlib

theorem algebra_221873 (a b : ℕ) (ha : a ≤ 10) (hb : b ≤ 10)
    (h : 5 * a - 2 * (10 - a) + 5 * b - 2 * (10 - b) = 58)
    (h' : 5 * a - 2 * (10 - a) = 14 + 5 * b - 2 * (10 - b)) :
    a = 8 := by
  omega
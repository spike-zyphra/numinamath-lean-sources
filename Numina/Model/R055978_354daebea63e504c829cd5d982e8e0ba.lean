import Mathlib

theorem calculus_276110 (a b c : ℕ) (ha : a ≤ 10) (hb : b ≤ 10) (hc : c ≤ 10)
    (h : a + b + c = 8) (h' : 3 * a + 4 * b + 5 * c = 33) :
    a ≤ 3 := by
  omega
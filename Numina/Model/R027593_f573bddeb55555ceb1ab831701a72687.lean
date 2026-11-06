import Mathlib

theorem number_theory_320873 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hsum : a + b + c = 100) :
    (max (max (a - b) (b - c)) (a - c)) + (max (max (b - a) (c - b)) (c - a)) +
    (max (max (c - a) (a - b)) (a - c)) ≤ 194 := by 
  omega
import Mathlib

theorem number_theory_198123 (a b c : ℤ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : 28 * a + 30 * b + 31 * c = 365) : a + b + c = 12 := by 
  omega
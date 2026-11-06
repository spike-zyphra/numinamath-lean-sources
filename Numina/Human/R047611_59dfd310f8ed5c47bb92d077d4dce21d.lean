import Mathlib

theorem number_theory_93865 (a b c : ℕ) (ha : a < 10) (hb : b < 10) (hc : 0 < c ∧ c < 10)
    (h : (7 * 100 + 10 * a + 2) - (4 * 100 + 8 * 10 + b) = (c * 100 + 7 * 10 + 3)) :
    a + b + c = 17 := by 
  omega
import Mathlib

theorem algebra_180868 (n : ℕ) (h : n > 0) (a b : ℕ)
    (ha : a * 5 + b * 6 = 153) (hb : a * 9 + b * 10 = 245) :
    a = 8 ∧ b = 2 := by
  omega
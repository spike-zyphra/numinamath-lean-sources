import Mathlib

theorem number_theory_194591 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 2^a * 9^b = 1000 * 2 + 100 * a + 10 * 9 + b) :
    a = 5 ∧ b = 2 := by
  interval_cases a <;> interval_cases b <;> omega
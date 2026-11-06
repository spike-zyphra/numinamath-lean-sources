import Mathlib

theorem number_theory_94882 (a b c: ℕ) (ha : a < 10) (hb : b < 10) (hc : c < 10)
(hN : 3194 = (100 * a + 10 * c + b) + (100 * b + 10 * a + c) +
(100 * b + 10 * c + a) + (100 * c + 10 * a + b) + (100 * c + 10 * b + a)) :
a = 3 ∧ b = 5 ∧ c = 8 := by
  have h1 : a ≤ 9 := by linarith
  have h2 : b ≤ 9 := by linarith
  have h3 : c ≤ 9 := by linarith
  interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega
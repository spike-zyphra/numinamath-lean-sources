import Mathlib

theorem number_theory_235482 (a b c : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a < 10 ∧ b < 10 ∧ c < 10) :
    (100 * a + 10 * b + c) + (100 * a + 10 * c + b) +
    (100 * b + 10 * a + c) + (100 * b + 10 * c + a) +
    (100 * c + 10 * a + b) + (100 * c + 10 * b + a) ≠ 2018 := by
  rcases h with ⟨ha1, hb1, hc1⟩
  interval_cases a <;> interval_cases b <;> omega
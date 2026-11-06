import Mathlib

theorem number_theory_7406 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 99 ∣ 32450000 + 1000 * a + 100 * b + 24) :
    a = 9 ∧ b = 7 := by
  interval_cases a <;> interval_cases b <;> norm_num at h <;> omega
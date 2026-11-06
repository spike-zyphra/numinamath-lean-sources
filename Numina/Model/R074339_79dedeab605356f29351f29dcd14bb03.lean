import Mathlib

theorem number_theory_219060 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a * b = 100) (h1 : ∀ d ∈ Nat.digits 10 a, d ≠ 0)
    (h2 : ∀ d ∈ Nat.digits 10 b, d ≠ 0) :
    a + b = 29 := by
  have h3 : a ≤ 100 := by
    nlinarith
  have h4 : b ≤ 100 := by
    nlinarith
  interval_cases a <;> interval_cases b <;> norm_num at h h1 h2 ⊢ <;> all_goals
    omega
import Mathlib

theorem number_theory_254172 (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (h : a ≠ b) (h1 : a < 50) (h2 : b < 50) (h3 : (a ^ 2) % 100 = (b ^ 2) % 100) :
    (a + b) / 2 = 10 ∨ (a + b) / 2 = 15 ∨ (a + b) / 2 = 20 ∨ (a + b) / 2 = 25 ∨
    (a + b) / 2 = 30 ∨ (a + b) / 2 = 35 ∨ (a + b) / 2 = 40 := by
  interval_cases a <;> interval_cases b
    <;> norm_num at h3 ⊢
    <;> omega
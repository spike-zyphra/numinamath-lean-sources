import Mathlib

theorem number_theory_240182 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h : 13 ∣ (200000 + 10000 * a + 1000 * 0 + 100 * b + 10 * 8 + 2)) :
    (a = 9 ∧ b = 0) ∨ (a = 6 ∧ b = 1) ∨ (a = 3 ∧ b = 2) ∨ (a = 0 ∧ b = 3) ∨
    (a = 7 ∧ b = 5) ∨ (a = 4 ∧ b = 6) ∨ (a = 1 ∧ b = 7) ∨ (a = 8 ∧ b = 9) := by
  have h1 : a < 10 := ha
  have h2 : b < 10 := hb
  interval_cases a <;> interval_cases b <;> norm_num at h ⊢ <;> omega
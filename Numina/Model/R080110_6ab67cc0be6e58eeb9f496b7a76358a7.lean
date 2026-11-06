import Mathlib

theorem number_theory_125055 (a b : ℕ) (ha : a < 10) (hb : b < 10)
    (h1 : (2018 * 100 + 10 * a + b) % 5 = 1) (h2 : (2018 * 100 + 10 * a + b) % 11 = 8) :
    a = 9 ∧ b = 1 ∨ a = 3 ∧ b = 6 := by 
  interval_cases a <;> interval_cases b <;> norm_num at h1 h2 ⊢ <;> try { tauto }
  <;> omega
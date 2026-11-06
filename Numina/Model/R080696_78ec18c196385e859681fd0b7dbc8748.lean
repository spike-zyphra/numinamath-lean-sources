import Mathlib

theorem number_theory_5855 (a b : ℕ) (h : 0 ≤ a ∧ a ≤ 9) (h' : 0 ≤ b ∧ b ≤ 9)
    (h'' : 12 ∣ 20224000 + 100 * a + 10 * b + 8) :
    a * b ≤ 56 := by
  rcases h with ⟨ha1, ha2⟩
  rcases h' with ⟨hb1, hb2⟩
  interval_cases a <;> interval_cases b <;> omega
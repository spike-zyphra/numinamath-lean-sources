import Mathlib

theorem number_theory_2079 (a b c : ℕ) (ha : 1 ≤ a ∧ a ≤ 9) (hb : 0 ≤ b ∧ b ≤ 9) (hc : 0 ≤ c ∧ c ≤ 9) (h : 100 * a + 10 * b + c = 4 * a * b * c) :
    a = 3 ∧ b = 8 ∧ c = 4 := by
  rcases ha with ⟨ha1, ha2⟩
  rcases hb with ⟨hb1, hb2⟩
  rcases hc with ⟨hc1, hc2⟩
  interval_cases a <;> interval_cases b <;> omega
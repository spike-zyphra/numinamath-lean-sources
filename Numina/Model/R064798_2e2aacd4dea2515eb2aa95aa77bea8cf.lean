import Mathlib

theorem number_theory_294704 (a b : ℕ) :
    a < 10 ∧ b < 10 ∧ 99 ∣ (a * 1000 + b * 100 + 3 * 10 + 2) ↔ (a = 6 ∧ b = 7) := by
  constructor
  · -- Forward direction: If the conditions hold, then a = 6 and b = 7
    intro h
    rcases h with ⟨ha, hb, hdiv⟩
    have h1 : a < 10 := ha
    have h2 : b < 10 := hb
    interval_cases a <;> interval_cases b <;> omega
  · -- Backward direction: If a = 6 and b = 7, then the divisibility holds
    rintro ⟨rfl, rfl⟩
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
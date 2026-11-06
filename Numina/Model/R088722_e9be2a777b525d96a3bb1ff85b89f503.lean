import Mathlib

theorem number_theory_5479 (a b : ℤ) : a^6 - 5 * b^6 + 87 = 0 ↔ False := by
  constructor
  · -- Forward direction: If a^6 - 5 * b^6 + 87 = 0 then False
    intro h
    have h1 : a^6 % 5 = 0 ∨ a^6 % 5 = 1 ∨ a^6 % 5 = 4 := by
      have h2 : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by
        omega
      rcases h2 with (h2 | h2 | h2 | h2 | h2) <;> norm_num [pow_succ, Int.add_emod, Int.mul_emod, h2] at *
    have h3 : a^6 % 5 = 3 := by
      omega
    omega
  · -- Backward direction: If False then a^6 - 5 * b^6 + 87 = 0
    intro h
    cases h
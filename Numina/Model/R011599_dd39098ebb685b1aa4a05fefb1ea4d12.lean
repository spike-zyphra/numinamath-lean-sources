import Mathlib

theorem number_theory_259171 (a b : ℤ) (ha: 0 ≤ a) (hb: 0 ≤ b):
a^2 = b * (b+7) ↔ (a=0 ∧ b=0) ∨ (a=12 ∧ b=9) := by
  constructor
  · -- Forward implication: if a^2 = b*(b+7), then either (0,0) or (12,9)
    intro h_eq
    have h2 : (2 * b + 7 : ℤ) ^ 2 - (2 * a : ℤ) ^ 2 = 49 := by
      nlinarith
    -- Factor this as a difference of squares:
    have h3 : (2 * b + 7 - 2 * a : ℤ) * (2 * b + 7 + 2 * a : ℤ) = 49 := by
      linarith [h2]
    have h4 : (2 * b + 7 - 2 * a : ℤ) ∣ (49 : ℤ) := by
      use (2 * b + 7 + 2 * a : ℤ)
      all_goals linarith [h3]
    have h5 : (2 * b + 7 - 2 * a : ℤ) ≤ (49 : ℤ) := by
      exact Int.le_of_dvd (show (0 : ℤ) < 49 by norm_num) h4
    have h6 : (2 * b + 7 - 2 * a : ℤ) ≥ (-49 : ℤ) := by
      have h7 : (- (2 * b + 7 - 2 * a : ℤ)) ∣ (49 : ℤ) := by
        exact Int.neg_dvd.2 h4
      have h8 : - (2 * b + 7 - 2 * a : ℤ) ≤ (49 : ℤ) := by
        exact Int.le_of_dvd (show (0 : ℤ) < 49 by norm_num) h7
      omega
    interval_cases h : (2 * b + 7 - 2 * a : ℤ) <;> omega
  · -- Backward implication: if either (0,0) or (12,9), then the equation holds.
    rintro (h1 | h2)
    · -- (a = 0 ∧ b = 0)
      rcases h1 with ⟨rfl, rfl⟩
      all_goals
      norm_num
    · -- (a = 12 ∧ b = 9)
      rcases h2 with ⟨rfl, rfl⟩
      all_goals
      norm_num
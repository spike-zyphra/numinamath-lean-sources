import Mathlib.Data.Int.Defs
import Mathlib.Tactic

open Int

theorem number_theory_104530 (x y : ℤ) : x^2 = y^2 + y + 1 ↔ (x = -1 ∧ y = -1) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 ∧ y = -1) ∨ (x = 1 ∧ y = 0) := by
  constructor
  · -- Assume x² = y² + y + 1, prove the disjunction
    intro h
    have h1 : 4 * x^2 = (2 * y + 1)^2 + 3 := by
      nlinarith
    have h2 : (2 * x - (2 * y + 1)) * (2 * x + (2 * y + 1)) = 3 := by
      nlinarith [h1]
    have h3 : (2 * x - (2 * y + 1)) ∣ 3 := by
      use (2 * x + (2 * y + 1))
      all_goals linarith
    have h4 : (2 * x - (2 * y + 1)) ≤ 3 := by
      apply Int.le_of_dvd (by norm_num) h3
    have h5 : (2 * x - (2 * y + 1)) ≥ -3 := by
      have h6 : -(2 * x - (2 * y + 1)) ∣ 3 := by
        exact Int.neg_dvd.2 h3
      have h7 : -(2 * x - (2 * y + 1)) ≤ 3 := by
        apply Int.le_of_dvd (by norm_num) h6
      omega
    interval_cases h8 : (2 * x - (2 * y + 1)) <;> omega
  · -- Assume the disjunction, prove x² = y² + y + 1
    rintro (h | h | h | h)
    · -- Case x = -1 ∧ y = -1
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case x = -1 ∧ y = 0
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case x = 1 ∧ y = -1
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
    · -- Case x = 1 ∧ y = 0
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      all_goals norm_num
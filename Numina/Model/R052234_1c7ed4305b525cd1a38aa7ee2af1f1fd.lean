import Mathlib

theorem algebra_237694 (x y : ℤ) : x * y - 7 * x - y = 3 ↔
    (x = 2 ∧ y = 17) ∨ (x = 0 ∧ y = -3) ∨ (x = 3 ∧ y = 12) ∨
    (x = -1 ∧ y = 2) ∨ (x = 6 ∧ y = 9) ∨ (x = -4 ∧ y = 5) ∨
    (x = 11 ∧ y = 8) ∨ (x = -9 ∧ y = 6) := by
  constructor
  · -- Forward implication: if (x, y) satisfies equation, then it is a solution.
    intro h
    have h1 : (x - 1) * (y - 7) = 10 := by
      nlinarith
    have h2 : x - 1 ∣ 10 := by 
      use y - 7
      all_goals linarith
    have h4 : x - 1 ≤ 10 := by 
      apply Int.le_of_dvd (by norm_num) h2
    have h5 : x - 1 ≥ -10 := by
      have h6 : -(x - 1) ∣ 10 := by
        exact Int.neg_dvd.2 h2
      have h7 : -(x - 1) ≤ 10 := by
        apply Int.le_of_dvd (by norm_num) h6
      linarith
    interval_cases h9 : x - 1 <;> omega
  · -- Backward implication: each given solution satisfies the equation.
    rintro (h | h | h | h | h | h | h | h)
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
    · rcases h with ⟨rfl, rfl⟩
      norm_num
import Mathlib

theorem number_theory_201276 (n : ℕ) :
    (n = 1 → (n - 1) = 0 ∧ (n + 1) = 2) ∧
    (n = 10 → (n - 1) = 9 ∧ (n + 1) = 11) ∧
    (n = 9 → (n - 1) = 8 ∧ (n + 1) = 10) ∧
    (n = 18 → (n - 1) = 17 ∧ (n + 1) = 19) := by
  constructor
  · -- Assume n = 1, prove (n - 1) = 0 ∧ (n + 1) = 2
    intro h
    rw [h]
    constructor
    · -- Show 1 - 1 = 0
      all_goals norm_num
    · -- Show 1 + 1 = 2
      all_goals norm_num
  constructor
  · -- Assume n = 10, prove (n - 1) = 9 ∧ (n + 1) = 11
    intro h
    rw [h]
    constructor
    · -- Show 10 - 1 = 9
      all_goals norm_num
    · -- Show 10 + 1 = 11
      all_goals norm_num
  constructor
  · -- Assume n = 9, prove (n - 1) = 8 ∧ (n + 1) = 10
    intro h
    rw [h]
    constructor
    · -- Show 9 - 1 = 8
      all_goals norm_num
    · -- Show 9 + 1 = 10
      all_goals norm_num
  · -- Assume n = 18, prove (n - 1) = 17 ∧ (n + 1) = 19
    intro h
    rw [h]
    constructor
    · -- Show 18 - 1 = 17
      all_goals norm_num
    · -- Show 18 + 1 = 19
      all_goals norm_num
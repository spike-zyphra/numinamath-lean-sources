import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_198375 {x : ℝ} :
  (|2 * x - 1| > x + 2 ↔ x < -1 / 3 ∨ x > 3) ∧
  (|2 * x - 1| ≤ x + 2 ↔ -1 / 3 ≤ x ∧ x ≤ 3) := by 
  constructor
  · -- First statement: |2 * x - 1| > x + 2 ↔ x < -1 / 3 ∨ x > 3
    constructor
    · -- Forward implication: |2 * x - 1| > x + 2 → x < -1 / 3 ∨ x > 3
      intro h
      by_cases h1 : 2 * x - 1 ≥ 0
      · -- Case where 2x - 1 ≥ 0, so |2x - 1| = 2x - 1
        rw [abs_of_nonneg h1] at h
        right
        linarith
      · -- Case where 2x - 1 < 0, so |2x - 1| = 1 - 2x
        rw [abs_of_neg (lt_of_not_ge h1)] at h
        left
        linarith
    · -- Backward implication: x < -1 / 3 ∨ x > 3 → |2 * x - 1| > x + 2
      rintro (h | h)
      · -- Case where x < -1/3
        have h3 : 2 * x - 1 < 0 := by linarith
        rw [abs_of_neg h3]
        linarith
      · -- Case where x > 3
        have h5 : 2 * x - 1 ≥ 0 := by linarith
        rw [abs_of_nonneg h5]
        linarith
  · -- Second statement: |2 * x - 1| ≤ x + 2 ↔ -1 / 3 ≤ x ∧ x ≤ 3
    constructor
    · -- Forward implication: |2 * x - 1| ≤ x + 2 → -1 / 3 ≤ x ∧ x ≤ 3
      intro h
      by_cases h1 : 2 * x - 1 ≥ 0
      · -- Case where 2x - 1 ≥ 0, so |2x - 1| = 2x - 1
        have h2 : |2 * x - 1| = 2 * x - 1 := by 
          rw [abs_of_nonneg h1]
        rw [h2] at h
        constructor
        · -- Prove -1/3 ≤ x
          nlinarith
        · -- Prove x ≤ 3
          nlinarith
      · -- Case where 2x - 1 < 0, so |2x - 1| = 1 - 2x
        have h2 : |2 * x - 1| = 1 - 2 * x := by 
          rw [abs_of_neg (lt_of_not_ge h1)]
          all_goals linarith
        rw [h2] at h
        constructor
        · -- Prove -1/3 ≤ x
          nlinarith
        · -- Prove x ≤ 3
          nlinarith
    · -- Backward implication: -1 / 3 ≤ x ∧ x ≤ 3 → |2 * x - 1| ≤ x + 2
      rintro ⟨h1, h2⟩
      by_cases h1' : 2 * x - 1 ≥ 0
      · -- Case where 2x - 1 ≥ 0, so |2x - 1| = 2x - 1
        have h3 : |2 * x - 1| = 2 * x - 1 := by 
          rw [abs_of_nonneg h1']
        rw [h3]
        all_goals linarith
      · -- Case where 2x - 1 < 0, so |2x - 1| = 1 - 2x
        have h4 : |2 * x - 1| = 1 - 2 * x := by 
          rw [abs_of_neg (lt_of_not_ge h1')]
          all_goals linarith
        rw [h4]
        all_goals linarith
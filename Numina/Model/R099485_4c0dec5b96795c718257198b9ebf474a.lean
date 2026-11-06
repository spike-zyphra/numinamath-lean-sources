import Mathlib

theorem algebra_7369 (x : ℝ) : |5 * x + 3| + |5 * x - 4| = 7 ↔
    -3 / 5 ≤ x ∧ x ≤ 4 / 5 := by
  constructor
  · -- Forward implication: if the equation holds, then the bounds on x hold
    intro h_eq
    by_cases h1 : 5 * x + 3 ≥ 0
    · -- Case where 5x + 3 ≥ 0, which implies x ≥ -3/5
      by_cases h2 : 5 * x - 4 ≥ 0
      · -- Case where both expressions are non-negative, which implies x ≥ 4/5
        rw [abs_of_nonneg h1, abs_of_nonneg h2] at h_eq
        constructor
        · linarith
        · linarith
      · -- Case where 5x + 3 ≥ 0, but 5x - 4 < 0, which implies -3/5 ≤ x ≤ 4/5
        rw [abs_of_nonneg h1, abs_of_neg (lt_of_not_ge h2)] at h_eq
        constructor
        · linarith
        · linarith
    · -- Case where 5x + 3 < 0, which implies x < -3/5
      by_cases h2 : 5 * x - 4 ≥ 0
      · -- Case where 5x + 3 < 0, but 5x - 4 ≥ 0, which is impossible
        rw [abs_of_neg (lt_of_not_ge h1), abs_of_nonneg h2] at h_eq
        constructor
        · linarith
        · linarith
      · -- Case where both expressions are negative, which implies x < -3/5
        rw [abs_of_neg (lt_of_not_ge h1), abs_of_neg (lt_of_not_ge h2)] at h_eq
        constructor
        · linarith
        · linarith
  · -- Backward implication: if the bounds hold, then the equation holds
    rintro ⟨h1, h2⟩
    have h3 : 5 * x + 3 ≥ 0 := by
      linarith
    have h4 : 5 * x - 4 ≤ 0 := by
      linarith
    rw [abs_of_nonneg h3, abs_of_nonpos h4]
    linarith
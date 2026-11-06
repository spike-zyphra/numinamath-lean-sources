import Mathlib

theorem algebra_216196 (x : ℝ) : abs (3 * x - 2) + abs (3 * x + 1) = 3 ↔
    -1 / 3 ≤ x ∧ x ≤ 2 / 3 := by
  constructor
  · -- Assume abs (3 * x - 2) + abs (3 * x + 1) = 3 prove -1/3 ≤ x ∧ x ≤ 2/3
    intro h
    constructor
    · -- Show -1/3 ≤ x
      by_cases h2 : x ≥ 2 / 3
      · -- x ≥ 2/3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        linarith
      · -- x < 2/3
        by_cases h3 : x ≥ -1 / 3
        · -- -1/3 ≤ x < 2/3
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
          linarith
        · -- x < -1/3
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
          linarith
    · -- Show x ≤ 2/3
      by_cases h3 : x ≥ 2 / 3
      · -- x ≥ 2/3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        linarith
      · -- x < 2/3
        by_cases h4 : x ≥ -1 / 3
        · -- -1/3 ≤ x < 2/3
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
          linarith
        · -- x < -1/3
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
          linarith
  · -- Assume -1/3 ≤ x ∧ x ≤ 2/3 prove abs (3 * x - 2) + abs (3 * x + 1) = 3
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ 2 / 3
    · -- x = 2/3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · -- x < 2/3
      by_cases h4 : x ≥ -1 / 3
      · -- -1/3 ≤ x < 2/3
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Contradiction, x ≥ -1/3 by assumption
        linarith
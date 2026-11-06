import Mathlib

theorem algebra_306983 (x1 x2 : ℝ) (h : abs (2 * x1 - 1) + abs (2 * x1 + 3) = 4) (h' : abs (2 * x2 - 1) + abs (2 * x2 + 3) = 4) (hx1 : x1 < x2) :
    -2 ≤ x1 - x2 ∧ x1 - x2 < 0 := by
  have h1 : -3 / 2 ≤ x1 := by
    by_cases h1 : 2 * x1 - 1 ≥ 0
    · -- Case 1: 2x1 - 1 ≥ 0 and 2x1 + 3 ≥ 0
      rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)] at h
      linarith
    · -- Case 2: 2x1 - 1 < 0
      by_cases h2 : 2 * x1 + 3 ≥ 0
      · -- Case 2a: 2x1 - 1 < 0 and 2x1 + 3 ≥ 0
        rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h
        linarith
      · -- Case 2b: 2x1 + 3 < 0
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
        linarith

  have h2 : -3 / 2 ≤ x2 := by
    by_cases h1 : 2 * x2 - 1 ≥ 0
    · -- Case 1: 2x2 - 1 ≥ 0 and 2x2 + 3 ≥ 0
      rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)] at h'
      linarith
    · -- Case 2: 2x2 - 1 < 0
      by_cases h2 : 2 * x2 + 3 ≥ 0
      · -- Case 2a: 2x2 - 1 < 0 and 2x2 + 3 ≥ 0
        rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h'
        linarith
      · -- Case 2b: 2x2 + 3 < 0
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h'
        linarith

  have h3 : x1 ≤ 1 / 2 := by
    by_cases h1 : 2 * x1 - 1 ≥ 0
    · -- Case 1: 2x1 - 1 ≥ 0 and 2x1 + 3 ≥ 0
      rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)] at h
      linarith
    · -- Case 2: 2x1 - 1 < 0
      by_cases h2 : 2 * x1 + 3 ≥ 0
      · -- Case 2a: 2x1 - 1 < 0 and 2x1 + 3 ≥ 0
        rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h
        linarith
      · -- Case 2b: 2x1 + 3 < 0
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
        linarith

  have h4 : x2 ≤ 1 / 2 := by
    by_cases h1 : 2 * x2 - 1 ≥ 0
    · -- Case 1: 2x2 - 1 ≥ 0 and 2x2 + 3 ≥ 0
      rw [abs_of_nonneg h1, abs_of_nonneg (by linarith)] at h'
      linarith
    · -- Case 2: 2x2 - 1 < 0
      by_cases h2 : 2 * x2 + 3 ≥ 0
      · -- Case 2a: 2x2 - 1 < 0 and 2x2 + 3 ≥ 0
        rw [abs_of_neg (by linarith), abs_of_nonneg h2] at h'
        linarith
      · -- Case 2b: 2x2 + 3 < 0
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h'
        linarith

  have h5 : x1 - x2 < 0 := by linarith

  have h6 : x1 - x2 ≥ -2 := by
    linarith [h1, h2, h3, h4]

  constructor <;> linarith [h5, h6]
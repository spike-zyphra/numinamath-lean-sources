import Mathlib

theorem algebra_327312 : ¬∃ x : ℝ, |2 * x - 5| + |3 * x - 7| + |5 * x - 11| = 2015 / 2016 := by
  rintro ⟨x, hx⟩
  by_cases h1 : 2 * x - 5 ≥ 0
  · -- Case 1: If 2x - 5 ≥ 0, so x ≥ 2.5
    rw [abs_of_nonneg h1] at hx
    by_cases h2 : 3 * x - 7 ≥ 0
    · -- Case 1a: If 3x - 7 ≥ 0, so x ≥ 2.3333
      rw [abs_of_nonneg h2] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Case 1a1: If 5x - 11 ≥ 0, so x ≥ 2.2
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Case 1a2: If 5x - 11 < 0, so x < 2.2
        rw [abs_of_neg (by linarith)] at hx
        linarith
    · -- Case 1b: If 3x - 7 < 0, so x < 2.3333
      rw [abs_of_neg (by linarith)] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Case 1b1: If 5x - 11 ≥ 0, so x ≥ 2.2
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Case 1b2: If 5x - 11 < 0, so x < 2.2
        rw [abs_of_neg (by linarith)] at hx
        linarith
  · -- Case 2: If 2x - 5 < 0, so x < 2.5
    rw [abs_of_neg (by linarith)] at hx
    by_cases h2 : 3 * x - 7 ≥ 0
    · -- Case 2a: If 3x - 7 ≥ 0, so x ≥ 2.3333
      rw [abs_of_nonneg h2] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Case 2a1: If 5x - 11 ≥ 0, so x ≥ 2.2
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Case 2a2: If 5x - 11 < 0, so x < 2.2
        rw [abs_of_neg (by linarith)] at hx
        linarith
    · -- Case 2b: If 3x - 7 < 0, so x < 2.3333
      rw [abs_of_neg (by linarith)] at hx
      by_cases h3 : 5 * x - 11 ≥ 0
      · -- Case 2b1: If 5x - 11 ≥ 0, so x ≥ 2.2
        rw [abs_of_nonneg h3] at hx
        linarith
      · -- Case 2b2: If 5x - 11 < 0, so x < 2.2
        rw [abs_of_neg (by linarith)] at hx
        linarith
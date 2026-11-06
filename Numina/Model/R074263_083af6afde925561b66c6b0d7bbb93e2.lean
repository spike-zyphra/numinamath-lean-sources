import Mathlib

theorem algebra_189892 (x : ℝ) :
    |2 * x ^ 2 - 9 * x + 15| ≥ 20 ↔ x ≤ -1 / 2 ∨ x ≥ 5 := by
  constructor
  · -- Forward direction: if |2x² - 9x + 15| ≥ 20, then x ≤ -1/2 ∨ x ≥ 5
    intro h
    by_cases h1 : 2 * x ^ 2 - 9 * x + 15 ≥ 0
    · -- Case 1: When 2x² - 9x + 15 ≥ 0, |A| = A
      have h2 : 2 * x^2 - 9 * x + 15 ≥ 20 := by
        rw [abs_of_nonneg h1] at h
        linarith
      have h3 : 2 * x^2 - 9 * x - 5 ≥ 0 := by linarith
      have h4 : x ≤ -1 / 2 ∨ x ≥ 5 := by
        by_cases h5 : x ≤ -1 / 2
        · -- Case 1a: If x ≤ -1/2
          left
          linarith
        · -- Case 1b: If x > -1/2
          push_neg at h5
          have h6 : x ≥ 5 := by
            nlinarith
          right
          linarith
      exact h4
    · -- Case 2: When 2x² - 9x + 15 < 0, |A| = -A
      have h2 : 2 * x^2 - 9 * x + 15 < 0 := by linarith
      have h3 : -(2 * x^2 - 9 * x + 15) ≥ 20 := by
        rw [abs_of_neg h2] at h
        linarith
      have h4 : 2 * x^2 - 9 * x + 35 ≤ 0 := by
        nlinarith
      -- Show that 2x^2 - 9x + 35 ≤ 0 is impossible since discriminant is negative
      nlinarith [show 2 * x ^ 2 - 9 * x + 35 > 0 from by nlinarith]
  · -- Backward direction: if x ≤ -1/2 ∨ x ≥ 5, then |2x² - 9x + 15| ≥ 20
    intro h
    cases h with
    | inl h1 =>
      have h4 : 2 * x^2 - 9 * x - 5 ≥ 0 := by
        nlinarith
      have h5 : 2 * x^2 - 9 * x + 15 ≥ 20 := by
        linarith
      have h6 : 2 * x^2 - 9 * x + 15 ≥ 0 := by
        linarith
      rw [abs_of_nonneg h6]
      linarith
    | inr h2 =>
      have h4 : 2 * x^2 - 9 * x - 5 ≥ 0 := by
        nlinarith
      have h5 : 2 * x^2 - 9 * x + 15 ≥ 20 := by
        linarith
      have h6 : 2 * x^2 - 9 * x + 15 ≥ 0 := by
        linarith
      rw [abs_of_nonneg h6]
      linarith
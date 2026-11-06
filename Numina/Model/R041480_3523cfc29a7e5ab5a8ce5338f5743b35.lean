import Mathlib

theorem inequalities_12658 (a : ℝ) : (∀ x : ℝ, abs (x + a) - abs (x + 1) ≤ 2 * a) ↔
    a ≥ 1 / 3 := by
  constructor
  · -- Assume inequality holds for all x, need to show a ≥ 1/3
    intro h
    have h1 := h (-1)
    have h3 : abs (-1 + a) ≤ 2 * a := by
      have h4 : abs (-1 + (1 : ℝ)) = 0 := by
        norm_num [abs_zero]
      have h5 : abs (-1 + a) - abs (-1 + (1 : ℝ)) ≤ 2 * a := by
        simpa using h1
      rw [h4] at h5
      linarith
    cases' abs_cases (-1 + a) with h4 h4
    · -- Case 1: -1 + a ≥ 0
      linarith
    · -- Case 2: -1 + a < 0
      linarith
  · -- Assume a ≥ 1/3, need to show inequality holds for all x
    intro ha x
    by_cases h1 : x + a ≥ 0
    · -- Case 1: x + a ≥ 0
      rw [abs_of_nonneg h1]
      by_cases h2 : x + 1 ≥ 0
      · -- Case 1a: x + 1 ≥ 0
        rw [abs_of_nonneg h2]
        linarith
      · -- Case 1b: x + 1 < 0
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith
    · -- Case 2: x + a < 0
      rw [abs_of_neg (lt_of_not_ge h1)]
      by_cases h2 : x + 1 ≥ 0
      · -- Case 2a: x + 1 ≥ 0
        rw [abs_of_nonneg h2]
        linarith
      · -- Case 2b: x + 1 < 0
        rw [abs_of_neg (lt_of_not_ge h2)]
        linarith
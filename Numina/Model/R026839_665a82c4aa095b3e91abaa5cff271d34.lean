import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_181071 (x : ℝ) : |x + 1| > 2 * |x + 2| ↔
    x ∈ Ioo (-3) (-5 / 3) := by
  constructor
  · -- Assume |x + 1| > 2 * |x + 2|, prove x ∈ Ioo (-3) (-5 / 3)
    intro h
    have h1 : |x + 1| > 2 * |x + 2| := h
    by_cases h2 : x ≥ -1
    · -- Case x ≥ -1
      rw [abs_of_nonneg (show x + 1 ≥ 0 by linarith), abs_of_nonneg (show x + 2 ≥ 0 by linarith)] at h1
      linarith
    · -- Case -2 ≤ x < -1 or x < -2
      by_cases h3 : x ≥ -2
      · -- Case -2 ≤ x < -1
        rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonneg (show x + 2 ≥ 0 by linarith)] at h1
        constructor
        · -- Show that -3 < x
          linarith
        · -- Show that x < -5/3
          linarith
      · -- Case x < -2
        rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonpos (show x + 2 ≤ 0 by linarith)] at h1
        constructor
        · -- Show that -3 < x
          linarith
        · -- Show that x < -5/3
          linarith
  · -- Assume x ∈ Ioo (-3) (-5 / 3), prove |x + 1| > 2 * |x + 2|
    rintro ⟨h1, h2⟩
    by_cases h3 : x ≥ -2
    · -- Case -2 ≤ x < -5/3
      rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonneg (show x + 2 ≥ 0 by linarith)]
      linarith
    · -- Case x < -2
      rw [abs_of_nonpos (show x + 1 ≤ 0 by linarith), abs_of_nonpos (show x + 2 ≤ 0 by linarith)]
      linarith
import Mathlib

open Real Set

theorem inequalities_271935 (a : ℝ) :
    (∃ x : ℝ, |x + 3| + |x - 5| < a) ↔ a > 8 := by
  constructor
  · -- Assume there exists an x such that |x + 3| + |x - 5| < a
    intro h
    rcases h with ⟨x, hx⟩
    have h1 : |x + 3| + |x - 5| ≥ 8 := by
      by_cases h2 : x ≥ 5
      · -- Case x ≥ 5
        rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonneg (show x - 5 ≥ 0 by linarith)]
        linarith
      · -- Case -3 ≤ x < 5
        by_cases h3 : x ≥ -3
        · -- Case -3 ≤ x < 5
          rw [abs_of_nonneg (show x + 3 ≥ 0 by linarith), abs_of_nonpos (show x - 5 ≤ 0 by linarith)]
          linarith
        · -- Case x < -3
          rw [abs_of_nonpos (show x + 3 ≤ 0 by linarith), abs_of_nonpos (show x - 5 ≤ 0 by linarith)]
          linarith
    linarith only [hx, h1]
  · -- Assume a > 8, we need to show there exists x such that |x + 3| + |x - 5| < a
    intro ha
    use 0
    have h2 : |(0 : ℝ) + 3| + |(0 : ℝ) - 5| = 8 := by
      norm_num [abs_of_nonneg, abs_of_nonpos]
    linarith only [h2, ha]
import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_198898 (a : ℝ) :
  {x : ℝ | abs (x - 1) - abs (x - 2) < a} =
  if a > 1 then univ else
  if a < -1 then ∅ else
  {x : ℝ | abs (x - 1) - abs (x - 2) < a} := by
  by_cases h1 : a > 1
  · -- Assume a > 1, then the solution set is ℝ.
    simp [h1]
    ext x
    simp
    have h2 : abs (x - 1) - abs (x - 2) ≤ 1 := by
      by_cases h11 : x ≥ 2
      · -- Assume x ≥ 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        all_goals linarith
      by_cases h12 : x ≥ 1
      · -- Assume 1 ≤ x < 2
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        all_goals linarith
      · -- Assume x < 1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        all_goals linarith
    linarith
  · -- a ≤ 1
    by_cases h2 : a < -1
    · -- Assume a < -1, then the solution set is ∅.
      simp [h1, h2]
      ext x
      simp
      have h3 : abs (x - 1) - abs (x - 2) ≥ -1 := by
        by_cases h11 : x ≥ 2
        · -- Assume x ≥ 2
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
          all_goals linarith
        by_cases h12 : x ≥ 1
        · -- Assume 1 ≤ x < 2
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          all_goals linarith
        · -- Assume x < 1
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          all_goals linarith
      linarith
    · -- -1 ≤ a ≤ 1
      simp [h1, h2]
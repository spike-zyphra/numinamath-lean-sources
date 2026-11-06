import Mathlib

open Real Set

theorem inequalities_198619 (a : ℝ) (ha : 0 < a) :
    (∃ x : ℝ, abs (x - 4) + abs (x - 3) < a) ↔ 1 < a := by
  constructor
  · -- Forward direction: if ∃ x such that |x - 4| + |x - 3| < a, then 1 < a
    intro h
    rcases h with ⟨x, hx⟩ 
    have h1 : abs (x - 4) + abs (x - 3) ≥ 1 := by
      by_cases h2 : x ≥ 4
      · -- Case x ≥ 4
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 3 ≤ x < 4
        by_cases h3 : x ≥ 3
        · rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
          linarith
        · -- Case x < 3
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
    linarith
  · -- Backward direction: if 1 < a, then ∃ x such that |x - 4| + |x - 3| < a
    intro h
    -- Let's choose x = 3.5 which is in the interval [3, 4)
    use 3.5

    have h1 : abs (3.5 - 4 : ℝ) + abs (3.5 - 3 : ℝ) = 1 := by
      norm_num [abs_of_nonpos, abs_of_nonneg]
      all_goals norm_num

    have h2 : abs (3.5 - 4 : ℝ) + abs (3.5 - 3 : ℝ) < a := by 
      linarith [h1, h]

    simpa using h2
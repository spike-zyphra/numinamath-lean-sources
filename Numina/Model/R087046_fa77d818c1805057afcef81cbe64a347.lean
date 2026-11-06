import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_304678 :
  IsLeast {a : ℝ | ∃ x, 2 * abs (x - 1) + 3 * abs (x - 3) ≤ a} 4 := by
  constructor
  · -- First, show that 4 is in the set
    use 3
    norm_num [abs]
  · -- Now, show that 4 is the least element in the set
    intro a ha
    obtain ⟨x, hx⟩ := ha  -- There exists some x such that 2|x-1| + 3|x-3| ≤ a
    by_contra h
    push_neg at h
    -- Assume for contradiction that a < 4, then 2|x-1| + 3|x-3| ≤ a < 4
    -- But we will show that for all real numbers x, 2|x-1| + 3|x-3| ≥ 4
    -- Let's analyze different cases based on the value of x
    have h1 : 2 * abs (x - 1) + 3 * abs (x - 3) ≥ 4 := by
      by_cases h2 : x ≥ 3
      · -- Case where x ≥ 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case where 1 ≤ x < 3
        by_cases h3 : x ≥ 1
        · -- Case where 1 ≤ x < 3
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · -- Case where x < 1
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
          linarith
    -- But we have 2|x-1| + 3|x-3| ≤ a and 2|x-1| + 3|x-3| ≥ 4
    -- So a must be at least 4, contradicts a < 4
    linarith -- This is a contradiction
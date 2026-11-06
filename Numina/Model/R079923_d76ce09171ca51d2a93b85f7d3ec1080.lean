import Mathlib

open Real Set

theorem inequalities_217918 (x : ℝ) :
    abs (5 - x) < abs (x - 2) + abs (7 - 2 * x) ↔
    x < 2 ∨ x > 3.5 := by
  constructor
  · -- Forward: inequality holds implies x in solution set
    intro h
    by_cases h1 : x < 2
    · -- Case x < 2
      left
      exact h1
    · -- Case where 2 ≤ x < 3.5 or x ≥ 3.5
      by_cases h2 : x < 3.5
      · -- Case where 2 ≤ x < 3.5
        have h3 : abs (5 - x) = 5 - x := by
          rw [abs_of_pos]
          linarith
        have h4 : 5 - x > 0 := by linarith
        have h5 : abs (x - 2) = x - 2 := by
          rw [abs_of_nonneg]
          linarith
        have h6 : x - 2 ≥ 0 := by linarith
        have h7 : abs (7 - 2 * x) = 7 - 2 * x := by
          rw [abs_of_pos]
          nlinarith
        have h8 : 7 - 2 * x > 0 := by nlinarith
        rw [h3, h5, h7] at h
        -- The inequality is false here
        nlinarith
      · -- Case where x ≥ 3.5
        have h2' : x ≥ 3.5 := by linarith
        by_cases h3 : x < 5
        · -- Case 3.5 ≤ x < 5
          have h4 : abs (5 - x) = 5 - x := by 
            rw [abs_of_pos]
            linarith
          have h5 : 5 - x > 0 := by linarith
          have h6 : abs (x - 2) = x - 2 := by 
            rw [abs_of_nonneg]
            linarith
          have h7 : abs (7 - 2 * x) = 2 * x - 7 := by 
            rw [abs_of_nonpos]
            nlinarith
            all_goals linarith
          have h8 : 7 - 2 * x ≤ 0 := by linarith
          rw [h4, h6, h7] at h
          right
          nlinarith
        · -- Case where x ≥ 5
          have h4 : abs (5 - x) = x - 5 := by 
            rw [abs_of_nonpos]
            all_goals linarith
          have h5 : 5 - x ≤ 0 := by linarith
          have h6 : abs (x - 2) = x - 2 := by 
            rw [abs_of_nonneg]
            linarith
          have h7 : abs (7 - 2 * x) = 2 * x - 7 := by 
            rw [abs_of_nonpos]
            all_goals linarith
          have h8 : 7 - 2 * x ≤ 0 := by linarith
          rw [h4, h6, h7] at h
          right
          nlinarith
  · -- Backward: x in solution set implies inequality holds
    rintro (h | h)
    · -- Case x < 2
      have h1 : abs (5 - x) = 5 - x := by
        rw [abs_of_pos]
        linarith
      have h2 : abs (x - 2) = 2 - x := by
        rw [abs_of_neg]
        all_goals linarith
      have h3 : abs (7 - 2 * x) = 7 - 2 * x := by 
        rw [abs_of_pos]
        nlinarith
      rw [h1, h2, h3]
      nlinarith
    · -- Case where x > 3.5
      have h2 : x ≥ 3.5 := by linarith
      -- Need to subcase here
      by_cases h3 : x < 5
      · -- Case 3.5 < x < 5
        have h4 : abs (5 - x) = 5 - x := by 
          rw [abs_of_pos]
          linarith
          -- since 5 > x
        have h5 : 5 - x > 0 := by linarith
        have h6 : abs (x - 2) = x - 2 := by 
          rw [abs_of_nonneg]
          linarith
        have h7 : abs (7 - 2 * x) = 2 * x - 7 := by 
          rw [abs_of_nonpos]
          all_goals nlinarith
        have h8 : 7 - 2 * x ≤ 0 := by nlinarith
        rw [h4, h6, h7]
        nlinarith
      · -- Case where x ≥ 5
        have h4 : abs (5 - x) = x - 5 := by 
          rw [abs_of_nonpos]
          all_goals linarith
        have h5 : 5 - x ≤ 0 := by linarith
        have h6 : abs (x - 2) = x - 2 := by 
          rw [abs_of_nonneg]
          linarith
        have h7 : abs (7 - 2 * x) = 2 * x - 7 := by 
          rw [abs_of_nonpos]
          all_goals nlinarith
        have h8 : 7 - 2 * x ≤ 0 := by nlinarith
        rw [h4, h6, h7]
        nlinarith
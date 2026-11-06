import Mathlib

theorem algebra_472 :
  IsLeast {p : ℚ | ∃ x : ℚ, p = abs (3 * x + 6) + abs (x - 3) + abs (2 * x - 6) + abs (x - 9)} 21 := by
  constructor
  · -- Show 21 is achievable, with x = 3.
    use 3
    norm_num [abs]
  · -- Show 21 is the least such value
    intro p hp
    rcases hp with ⟨x, hx⟩
    rw [hx]
    have h : abs (3 * x + 6) + abs (x - 3) + abs (2 * x - 6) + abs (x - 9) ≥ (21 : ℚ) := by
      by_cases h1 : x ≥ 9
      · -- Case 1: x ≥ 9
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Now x < 9
        by_cases h2 : x ≥ 3
        · -- Case 2: 3 ≤ x < 9
          by_cases h3 : x ≥ 6
          · -- Subcase 2.1: 6 ≤ x < 9
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
            all_goals linarith
          · -- Subcase 2.2: 3 ≤ x < 6
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
            all_goals linarith
        · -- Now x < 3
          by_cases h3 : x ≥ -2
          · -- Case 3: -2 ≤ x < 3
            rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            all_goals linarith
          · -- Case 4: x < -2
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            all_goals linarith
    linarith
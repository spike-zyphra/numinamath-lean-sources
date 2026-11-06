import Mathlib

theorem algebra_11557 :
    IsLeast {x | ∃ t : ℝ, x = abs (t - 1) + abs (t - 3) + abs (t - 5) + abs (t - 7)} 8 := by
  constructor
  · -- Show 8 is in the set.
    use 4
    norm_num [abs]
  · -- Show it's minimal
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : abs (t - 1) + abs (t - 3) + abs (t - 5) + abs (t - 7) ≥ 8 := by
      by_cases h1 : t ≥ 7
      · -- Case 1: t ≥ 7
        rw [abs_of_nonneg (show t - 1 ≥ 0 by linarith),
            abs_of_nonneg (show t - 3 ≥ 0 by linarith),
            abs_of_nonneg (show t - 5 ≥ 0 by linarith),
            abs_of_nonneg (show t - 7 ≥ 0 by linarith)]
        linarith
      by_cases h2 : t ≥ 5
      · -- Case 2: 5 ≤ t < 7
        rw [abs_of_nonneg (show t - 1 ≥ 0 by linarith),
            abs_of_nonneg (show t - 3 ≥ 0 by linarith),
            abs_of_nonneg (show t - 5 ≥ 0 by linarith),
            abs_of_neg (show t - 7 < 0 by linarith)]
        linarith
      by_cases h3 : t ≥ 3
      · -- Case 3: 3 ≤ t < 5
        rw [abs_of_nonneg (show t - 1 ≥ 0 by linarith),
            abs_of_nonneg (show t - 3 ≥ 0 by linarith),
            abs_of_neg (show t - 5 < 0 by linarith),
            abs_of_neg (show t - 7 < 0 by linarith)]
        linarith
      by_cases h4 : t ≥ 1
      · -- Case 4: 1 ≤ t < 3
        rw [abs_of_nonneg (show t - 1 ≥ 0 by linarith),
            abs_of_neg (show t - 3 < 0 by linarith),
            abs_of_neg (show t - 5 < 0 by linarith),
            abs_of_neg (show t - 7 < 0 by linarith)]
        linarith
      · -- Case 5: t < 1
        rw [abs_of_neg (show t - 1 < 0 by linarith),
            abs_of_neg (show t - 3 < 0 by linarith),
            abs_of_neg (show t - 5 < 0 by linarith),
            abs_of_neg (show t - 7 < 0 by linarith)]
        linarith
    linarith [ht, h1]
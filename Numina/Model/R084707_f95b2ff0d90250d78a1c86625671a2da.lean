import Mathlib

theorem algebra_188803 :
    IsLeast {x | ∃ a : ℝ, x = abs (a - 1) + abs (a - 2) + abs (a - 3)} 2 := by
  constructor
  · -- Show 2 is in the set
    use (2 : ℝ)
    norm_num [abs]
  · -- Show there is no smaller x in the set
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : abs (a - 1) + abs (a - 2) + abs (a - 3) ≥ 2 := by
      by_cases h4 : a ≥ 3
      · -- Case a ≥ 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 2 ≤ a < 3
        by_cases h3 : a ≥ 2
        · -- Case 2 ≤ a < 3
          rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
          linarith
        · -- Case 1 ≤ a < 2
          by_cases h2 : a ≥ 1
          · -- Case 1 ≤ a < 2
            rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
          · -- Case a < 1
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
    linarith
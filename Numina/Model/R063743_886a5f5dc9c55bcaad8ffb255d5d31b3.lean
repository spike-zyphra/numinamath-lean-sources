import Mathlib

theorem algebra_5002 :
  IsLeast {y : ℝ | ∃ x, y = |x - 3| + |x - 7| + |x - 11|} 8 := by
  constructor
  · -- Show that 8 is achievable at x = 7
    use 7
    norm_num
  · -- Show that 8 is a lower bound
    intro y hy
    rcases hy with ⟨x, hx⟩
    rw [hx]
    have h1 : |x - 3| + |x - 7| + |x - 11| ≥ 8 := by
      by_cases h1 : x ≥ 11
      · -- Case 4: x ≥ 11
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 3: 7 ≤ x < 11
        by_cases h2 : x ≥ 7
        · -- Case 3: 7 ≤ x < 11
          by_cases h3 : x < 11
          · -- Case 3: 7 ≤ x < 11
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
            linarith
          · -- Case 4: x ≥ 11
            rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
            linarith
        · -- Case 2: x < 7
          by_cases h4 : x ≥ 3
          · -- Case 2: 3 ≤ x < 7
            rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
          · -- Case 1: x < 3
            rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
            linarith
    linarith
import Mathlib

theorem algebra_4902 :
  IsLeast {y : ℝ | ∃ x, y = |x - 8| + |x - 6| + |x + 2| + |x + 3|} 19 := by
  constructor
  · -- Show 19 is in the set
    use 2
    norm_num [abs]
    all_goals norm_num
  · -- Show 19 is the least element in the set
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : |x - 8| + |x - 6| + |x + 2| + |x + 3| ≥ 19 := by
      by_cases h1 : x ≥ 8
      · -- Case 1: x ≥ 8
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h2 : x ≥ 6
      · -- Case 2: 6 ≤ x < 8
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h3 : x ≥ -2
      · -- Case 3: -2 ≤ x < 6
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h4 : x ≥ -3
      · -- Case 4: -3 ≤ x < -2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- Case 5: x < -3
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    linarith [h1, hx]
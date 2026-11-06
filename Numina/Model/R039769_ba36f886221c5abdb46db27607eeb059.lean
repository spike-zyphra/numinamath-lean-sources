import Mathlib

theorem algebra_2985 (x : ℝ) :
  IsLeast {5 * abs (x - 6) + 4 * abs (x - 3) + 2 * abs (x - 2) + 3 * abs x + abs (x + 6) | x : ℝ} 35 := by
  constructor
  · -- Show that 35 is in the set
    use 3
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that 35 is the least element in the set
    intro s
    rintro ⟨x, hx⟩
    have h1 : 5 * abs (x - 6) + 4 * abs (x - 3) + 2 * abs (x - 2) + 3 * abs x + abs (x + 6) ≥ 35 := by
      by_cases h1 : x ≥ 6
      · -- Case 1: x ≥ 6
        rw [abs_of_nonneg (show x - 6 ≥ 0 by linarith), abs_of_nonneg (show x - 3 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show x + 6 ≥ 0 by linarith)]
        linarith
      by_cases h2 : x ≥ 3
      · -- Case 2: 3 ≤ x < 6
        rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonneg (show x - 3 ≥ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show x + 6 ≥ 0 by linarith)]
        linarith
      by_cases h3 : x ≥ 2
      · -- Case 3: 2 ≤ x < 3
        rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonneg (show x - 2 ≥ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show x + 6 ≥ 0 by linarith)]
        linarith
      by_cases h4 : x ≥ 0
      · -- Case 4: 0 ≤ x < 2
        rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith), abs_of_nonneg (show x ≥ 0 by linarith), abs_of_nonneg (show x + 6 ≥ 0 by linarith)]
        linarith
      by_cases h5 : x ≥ -6
      · -- Case 5: -6 ≤ x < 0
        rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith), abs_of_nonpos (show x ≤ 0 by linarith), abs_of_nonneg (show x + 6 ≥ 0 by linarith)]
        linarith
      · -- Case 6: x < -6
        rw [abs_of_nonpos (show x - 6 ≤ 0 by linarith), abs_of_nonpos (show x - 3 ≤ 0 by linarith), abs_of_nonpos (show x - 2 ≤ 0 by linarith), abs_of_nonpos (show x ≤ 0 by linarith), abs_of_nonpos (show x + 6 ≤ 0 by linarith)]
        linarith
    linarith [h1, hx]
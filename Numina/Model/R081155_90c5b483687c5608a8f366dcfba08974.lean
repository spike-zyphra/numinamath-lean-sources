import Mathlib

theorem algebra_3590 :
    IsLeast {y : ℝ | ∃ x, y = abs (x - 20) + abs (x + 17) + abs (x + 3) + abs (x - 26)} 66 := by
  constructor
  · -- First part: prove 66 is in the set
    use 20
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Second part: prove the minimum of the set is 66
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : abs (x - 20) + abs (x + 17) + abs (x + 3) + abs (x - 26) ≥ 66 := by
      by_cases h1 : x ≥ 26
      · -- Case 1: x ≥ 26
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      by_cases h2 : x ≥ 20
      · -- Case 2: 20 ≤ x < 26
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
      by_cases h3 : x ≥ -3
      · -- Case 3: -3 ≤ x < 20
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        linarith
      by_cases h4 : x ≥ -17
      · -- Case 4: -17 ≤ x < -3
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
      · -- Case 5: x < -17
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    linarith [hx, h1]
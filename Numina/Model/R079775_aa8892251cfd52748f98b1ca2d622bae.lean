import Mathlib

open Real Set

theorem algebra_3811 :
    IsLeast {y : ℝ | ∃ x : ℝ, y = 4 * abs (x + 2) + 2 * abs (x - 0) + 2 * abs (x - 2) + abs (x - 3)} 15 := by 
  constructor 
  · -- Let's prove 15 is achievable (when x = 0)
    use 0
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Now let's prove 15 is the smallest possible value
    intro y hy
    rcases hy with ⟨x, hx⟩
    -- The function is continuous with possible slope changes at x = -2, 0, 2, 3
    by_cases h1 : x ≥ 3
    · -- Case x ≥ 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at hx
      linarith
    by_cases h2 : x ≥ 2
    · -- Case 2 ≤ x < 3
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith)] at hx
      linarith
    by_cases h3 : x ≥ 0
    · -- Case 0 ≤ x < 2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at hx
      linarith
    by_cases h4 : x ≥ -2
    · -- Case -2 ≤ x < 0
      rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at hx
      linarith
    · -- Case x < -2
      rw [abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith), abs_of_neg (by linarith)] at hx
      linarith
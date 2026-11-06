import Mathlib

open Real Set

theorem algebra_3174 (x : ℝ) :
    IsLeast {y | ∃ x : ℝ, y = abs (x - 4) + 2 * abs (x - 3) + 3 * abs (x - 2) + 4 * abs (x - 1)} 8 := by
  constructor
  · -- Show that 8 belongs to the set, i.e., there exists some x such that the expression equals 8.
    use 2
    norm_num [abs_of_nonneg, abs_of_nonpos]
    <;> norm_num
  · -- Show that 8 is the least in the set
    intro y hy
    rcases hy with ⟨x, rfl⟩
    by_cases h1 : x ≥ 4
    · -- Case 1: x ≥ 4
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    by_cases h2 : x ≥ 3
    · -- Case 2: 3 ≤ x < 4
      rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    by_cases h3 : x ≥ 2
    · -- Case 3: 2 ≤ x < 3
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    by_cases h4 : x ≥ 1
    · -- Case 4: 1 ≤ x < 2
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
      linarith
    -- Case 5: x < 1
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
    linarith
import Mathlib

open Real Set

theorem algebra_237293 :
  IsLeast {x : ℝ | ∃ a b : ℝ, x = a^2 + b^2 + abs (a * b - 1) + abs (a * b - 4)} 5 := by
  constructor
  · -- Show 5 is achieved, using a = 1, b = 1
    use 1, 1
    norm_num [abs_of_nonneg, abs_of_nonpos]
  · -- Show that 5 is the minimum value
    intro x hx
    rcases hx with ⟨a, b, h_eq⟩
    by_cases h1 : a * b ≥ 4
    · -- Case 1: a * b ≥ 4
      rw [h_eq]
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      nlinarith [sq_nonneg (a - b)]
    · -- Consider next case
      by_cases h2 : a * b ≥ 1
      · -- Case 2: 1 ≤ a * b < 4
        rw [h_eq]
        rw [abs_of_nonneg (by linarith), abs_of_neg (by linarith)]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
      · -- Case 3: a * b < 1
        rw [h_eq]
        rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
        nlinarith [sq_nonneg (a - b), sq_nonneg (a * b - 1)]
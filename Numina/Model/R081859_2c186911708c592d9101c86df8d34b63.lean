import Mathlib

open Real Set

theorem algebra_9021 :
    IsLeast {M | ∃ x y : ℝ, 0 ≤ x ∧ x ≤ y ∧ y ≤ 1 ∧ M = max (max (x * y) (x * y - x - y + 1)) (x + y - 2 * x * y)} (4 / 9) := by
  constructor
  · -- First part: proving 4/9 is achievable by x = y = 2/3
    use 2 / 3, 2 / 3
    norm_num [max_eq_left, max_eq_right]
  
  · -- Second part: proving 4/9 is minimal
    intro M h
    rcases h with ⟨x, y, hx, hxy, hy, hM⟩
    rw [hM]
    -- Establish the maximum value
    by_cases h1 : x * y ≥ x * y - x - y + 1
    · -- Case where max (x * y) (x * y - x - y + 1) = x * y
      rw [max_eq_left h1]
      -- Now compare x y and x + y - 2 x y
      by_cases h2 : x * y ≥ x + y - 2 * x * y
      · -- Case where max is x * y
        rw [max_eq_left h2]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3)]
      · -- Case where max is x + y - 2 x y
        rw [max_eq_right (le_of_not_le h2)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3)]
    · -- Case where max (x * y) (x * y - x - y + 1) = x * y - x - y + 1
      rw [max_eq_right (le_of_not_le h1)]
      -- Now compare x y - x - y + 1 and x + y - 2 x y
      by_cases h3 : x * y - x - y + 1 ≥ x + y - 2 * x * y
      · -- Case where max is x y - x - y + 1
        rw [max_eq_left h3]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3)]
      · -- Case where max is x + y - 2 x y
        rw [max_eq_right (le_of_not_le h3)]
        nlinarith [sq_nonneg (x - y), sq_nonneg (x - 2 / 3), sq_nonneg (y - 2 / 3)]
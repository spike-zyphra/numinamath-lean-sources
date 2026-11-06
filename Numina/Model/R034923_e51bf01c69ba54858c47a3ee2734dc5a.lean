import Mathlib

theorem algebra_2624 : {x : ℝ | (abs (x^2 - 1) - x * abs (x + 1)) = 0} = {-1, 1/2} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Assume x in the solution set
    intro h
    have h1 : abs (x^2 - 1) = x * abs (x + 1) := by linarith
    by_cases h2 : x < -1
    · -- Case 1: x < -1
      rw [abs_of_pos (show x ^ 2 - 1 > 0 by nlinarith),
          abs_of_neg (show x + 1 < 0 by linarith)] at h1
      nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1)]
    · -- Case 2: -1 ≤ x ≤ 1 or x > 1
      by_cases h3 : x ≤ 1
      · -- Case 2a: -1 ≤ x ≤ 1
        rw [abs_of_nonpos (show x ^ 2 - 1 ≤ 0 by nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 1)])] at h1
        rw [abs_of_nonneg (show x + 1 ≥ 0 by nlinarith)] at h1
        have h2 : (x - 1 / 2) * (x + 1) = 0 := by nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1)]
        cases' (mul_eq_zero.1 h2) with h3 h4
        · right
          linarith
        · left
          linarith
      · -- Case 2b: x > 1
        rw [abs_of_pos (show x ^ 2 - 1 > 0 by nlinarith),
            abs_of_pos (show x + 1 > 0 by linarith)] at h1
        nlinarith [sq_nonneg (x - 1 / 2), sq_nonneg (x + 1)]
  · -- Show that both -1 and 1/2 satisfy the equation
    rintro (rfl | rfl)
    · -- Case x = -1
      norm_num [abs_of_nonneg, abs_of_nonpos]
    · -- Case x = 1/2
      norm_num [abs_of_nonneg, abs_of_nonpos]
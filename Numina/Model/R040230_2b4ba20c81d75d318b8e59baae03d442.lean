import Mathlib

theorem algebra_96947 : Set.Infinite {x : ℝ | abs (x - 2) + abs (x - 3) = 1} := by

  have h1 : {x : ℝ | abs (x - 2) + abs (x - 3) = 1} = Set.Icc (2) (3) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume $|x-2| + |x-3| = 1$ holds
      intro h
      by_cases h2 : x ≥ 3
      · -- Case x ≥ 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        constructor <;> linarith
      · -- Case 2 ≤ x < 3
        by_cases h2' : x ≥ 2
        · -- Case 2 ≤ x < 3
          rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)] at h
          constructor <;> linarith
        · -- Case x < 2
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
          linarith
    · -- Assume $2 \leq x \leq 3$ holds
      rintro ⟨h2, h3⟩
      by_cases h2' : x ≥ 3
      · -- Case x = 3
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        all_goals linarith
      · -- Case 2 ≤ x < 3
        rw [abs_of_nonneg (by linarith), abs_of_nonpos (by linarith)]
        all_goals linarith
  rw [h1]
  apply Set.Icc_infinite
  all_goals norm_num
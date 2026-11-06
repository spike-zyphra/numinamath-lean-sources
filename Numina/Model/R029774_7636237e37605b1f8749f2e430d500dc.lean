import Mathlib

theorem algebra_326109 : Set.Infinite {x : ℝ | abs (x - 2) + abs (x + 1) = 3} := by
  have h1 : {x : ℝ | abs (x - 2) + abs (x + 1) = 3} = Set.Icc (-1) (2) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume abs (x - 2) + abs (x + 1) = 3 prove x ∈ Set.Icc (-1) (2)
      intro h
      by_cases h2 : x ≥ 2
      · -- x ≥ 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        constructor
        · linarith
        · linarith
      · -- x < 2
        by_cases h3 : x ≥ -1
        · -- -1 ≤ x < 2
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
          constructor
          · linarith
          · linarith
        · -- x < -1
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
          constructor
          · linarith
          · linarith
    · -- Assume x ∈ Set.Icc (-1) (2) prove abs (x - 2) + abs (x + 1) = 3
      rintro ⟨h1, h2⟩
      by_cases h3 : x ≥ 2
      · -- x = 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
        linarith
      · -- -1 ≤ x < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)]
        linarith
  rw [h1]
  apply Set.Icc_infinite
  all_goals norm_num
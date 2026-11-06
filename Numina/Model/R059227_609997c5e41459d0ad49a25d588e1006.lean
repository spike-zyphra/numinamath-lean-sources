import Mathlib

theorem algebra_150705 : {x : ℝ | abs (x - 2) + abs (x - 3) = 1}.Infinite := by
  have h1 : {x : ℝ | abs (x - 2) + abs (x - 3) = 1} = Set.Icc 2 3 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume abs (x - 2) + abs (x - 3) = 1, prove 2 ≤ x ∧ x ≤ 3
      intro h
      by_cases h2 : x ≥ 3
      · -- x ≥ 3
        rw [abs_of_nonneg (by linarith : x - 2 ≥ 0), abs_of_nonneg (by linarith : x - 3 ≥ 0)] at h
        constructor <;> linarith
      by_cases h3 : x ≥ 2
      · -- 2 ≤ x < 3
        rw [abs_of_nonneg (by linarith : x - 2 ≥ 0), abs_of_nonpos (by linarith : x - 3 ≤ 0)] at h
        constructor <;> linarith
      · -- x < 2
        rw [abs_of_nonpos (by linarith : x - 2 ≤ 0), abs_of_nonpos (by linarith : x - 3 ≤ 0)] at h
        linarith
    · -- Assume 2 ≤ x ∧ x ≤ 3, prove abs (x - 2) + abs (x - 3) = 1
      rintro ⟨h2, h3⟩
      by_cases h4 : x ≥ 3
      · -- x = 3
        rw [abs_of_nonneg (by linarith : x - 2 ≥ 0), abs_of_nonneg (by linarith : x - 3 ≥ 0)]
        linarith
      · -- 2 ≤ x < 3
        rw [abs_of_nonneg (by linarith : x - 2 ≥ 0), abs_of_nonpos (by linarith : x - 3 ≤ 0)]
        linarith
  rw [h1]
  apply Set.Icc_infinite
  all_goals norm_num
import Mathlib

theorem algebra_318679 : Set.Infinite {x : ℝ | abs (x - 2) + abs (x - 3) = 1} := by 
  have h1 : {x : ℝ | abs (x - 2) + abs (x - 3) = 1} = Set.Icc 2 3 := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    constructor
    · -- Assume abs (x - 2) + abs (x - 3) = 1, we need to show 2 ≤ x ≤ 3
      intro h
      by_cases h2 : x ≥ 2
      · by_cases h3 : x ≥ 3
        · -- x ≥ 3
          rw [abs_of_nonneg (show (x - 2) ≥ 0 by linarith), abs_of_nonneg (show (x - 3) ≥ 0 by linarith)] at h
          constructor <;> linarith 
        · -- 2 ≤ x < 3
          rw [abs_of_nonneg (show (x - 2) ≥ 0 by linarith), abs_of_nonpos (show (x - 3) ≤ 0 by linarith)] at h 
          constructor <;> linarith 
      · -- x < 2
        rw [abs_of_nonpos (show (x - 2) ≤ 0 by linarith), abs_of_nonpos (show (x - 3) ≤ 0 by linarith)] at h
        -- impossible
        linarith 
    · -- Assume 2 ≤ x ≤ 3, we need to prove abs (x - 2) + abs (x - 3) = 1
      rintro ⟨h2, h3⟩
      by_cases h4 : x ≥ 3
      · -- x = 3
        rw [abs_of_nonneg (show (x - 2) ≥ 0 by linarith), abs_of_nonneg (show (x - 3) ≥ 0 by linarith)]
        linarith 
      · -- 2 ≤ x < 3
        rw [abs_of_nonneg (show (x - 2) ≥ 0 by linarith), abs_of_nonpos (show (x - 3) ≤ 0 by linarith)]
        linarith 
  rw [h1]
  apply Set.Icc_infinite
  all_goals norm_num
import Mathlib

theorem algebra_12730 : ∑ᶠ x ∈ {x : ℝ | x = |2 * x - abs (60 - 2 * x)|}, x = 92 := by

  have h1 : {x : ℝ | x = |2 * x - abs (60 - 2 * x)|} = {12, 20, 60} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x = |2 * x - abs (60 - 2 * x)|, prove x ∈ {12, 20, 60}
      intro hx
      have h2 : x = |2 * x - abs (60 - 2 * x)| := hx
      by_cases h3 : (60 - 2 * x : ℝ) ≥ 0
      · -- If 60 - 2 * x ≥ 0, then abs (60 - 2 * x) = 60 - 2 * x
        have h4 : abs (60 - 2 * x) = 60 - 2 * x := by
          rw [abs_of_nonneg h3]
        rw [h4] at h2
        by_cases h5 : (2 * x - (60 - 2 * x) : ℝ) ≥ 0
        · -- If 2 * x - (60 - 2 * x) ≥ 0, then abs ... = 4x - 60
          have h6 : abs (2 * x - (60 - 2 * x)) = 4 * x - 60 := by
            have h7 : (2 * x - (60 - 2 * x) : ℝ) = 4 * x - 60 := by
              linarith
            rw [h7]
            rw [abs_of_nonneg (by linarith)]
          rw [h6] at h2
          have h8 : x = 20 := by linarith
          simp [h8]
        · -- If 2 * x - (60 - 2 * x) < 0, then abs ... = 60 - 4x
          have h6 : abs (2 * x - (60 - 2 * x)) = 60 - 4 * x := by
            have h7 : (2 * x - (60 - 2 * x) : ℝ) = 4 * x - 60 := by
              linarith
            rw [h7]
            rw [abs_of_neg (by linarith)]
            <;> linarith
          rw [h6] at h2
          have h8 : x = 12 := by linarith
          simp [h8]
      · -- If 60 - 2 * x < 0, then abs (60 - 2 * x) = 2x - 60
        have h4 : abs (60 - 2 * x) = 2 * x - 60 := by
          rw [abs_of_neg (by linarith)]
          all_goals linarith
        rw [h4] at h2
        have h5 : abs (2 * x - (2 * x - 60)) = 60 := by
          have h6 : 2 * x - (2 * x - 60) = (60 : ℝ) := by
            linarith
          rw [h6]
          norm_num [abs_of_nonneg]
        rw [h5] at h2
        have h8 : x = 60 := by linarith
        simp [h8]
    · -- Assume x ∈ {12, 20, 60}, prove x = |2 * x - abs (60 - 2 * x)|
      rintro (rfl | rfl | rfl)
      · -- Check x = 12
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Check x = 20
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Check x = 60
        norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
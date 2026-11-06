import Mathlib
open Real

theorem algebra_98407 : ∑ᶠ x ∈ {x : ℝ | x = abs (2 * x - abs (60 - 2 * x))}, x = 92 := by
  have h1 : {x : ℝ | x = abs (2 * x - abs (60 - 2 * x))} = {12, 20, 60} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Forward direction: equation solving
      intro h_eq
      by_cases h2 : 60 - 2 * x ≥ 0
      · -- If 60 - 2x ≥ 0, then abs (60 - 2 * x) = 60 - 2 * x
        have h3 : abs (60 - 2 * x) = 60 - 2 * x := by
          rw [abs_of_nonneg h2]
        have h4 : abs (2 * x - abs (60 - 2 * x)) = abs (4 * x - 60) := by
          rw [h3]
          have h5 : 2 * x - (60 - 2 * x) = 4 * x - 60 := by ring
          rw [h5]
        rw [h4] at h_eq
        by_cases h5 : 4 * x - 60 ≥ 0
        · -- Then abs (4 * x - 60) = 4 * x - 60
          have h6 : abs (4 * x - 60) = 4 * x - 60 := by
            rw [abs_of_nonneg h5]
          rw [h6] at h_eq
          have hx1 : x = 20 := by linarith
          simp [hx1]
          <;> norm_num
        · -- Then abs (4 * x - 60) = 60 - 4 * x
          have h7 : abs (4 * x - 60) = 60 - 4 * x := by
            rw [abs_of_neg (by linarith)]
            <;> linarith
          rw [h7] at h_eq
          have hx2 : x = 12 := by linarith
          simp [hx2]
          <;> norm_num
      · -- If 60 - 2x < 0, abs (60 - 2 * x) = 2 * x - 60
        have h8 : abs (60 - 2 * x) = 2 * x - 60 := by
          rw [abs_of_neg (by linarith)]
          <;> linarith
        have h9 : abs (2 * x - abs (60 - 2 * x)) = 60 := by
          rw [h8]
          have h10 : 2 * x - (2 * x - 60) = 60 := by linarith
          rw [h10]
          <;> norm_num [abs_of_nonneg]
        rw [h9] at h_eq
        have hx3 : x = 60 := by linarith
        simp [hx3]
        <;> norm_num
    · -- Backward direction: checking solutions
      rintro (rfl | rfl | rfl)
      · -- Check 12
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Check 20
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Check 60
        norm_num [abs_of_nonneg, abs_of_nonpos]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> norm_num
  <;> ring
  all_goals norm_num
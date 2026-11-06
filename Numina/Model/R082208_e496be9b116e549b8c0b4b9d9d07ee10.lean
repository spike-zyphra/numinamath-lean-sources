import Mathlib

theorem algebra_199394 (B : ℤ) (hB : B = 3) :
    {x : ℤ | abs (x - 2) + abs (x + 1) = B}.encard = 4 := by
  rw [hB]
  have h1 : {x : ℤ | abs (x - 2) + abs (x + 1) = 3} = {-1, 0, 1, 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- If abs (x - 2) + abs (x + 1) = 3, then x ∈ {-1, 0, 1, 2}
      intro h
      have h2 : abs (x - 2) + abs (x + 1) = 3 := h
      by_cases h3 : x ≥ 2
      · -- Case where x ≥ 2
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h2
        omega
      · -- Case where x < 2
        by_cases h4 : x ≥ -1
        · -- Case where -1 ≤ x < 2
          rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h2
          omega
        · -- Case where x < -1
          rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h2
          omega
    · -- If x ∈ {-1, 0, 1, 2}, then abs (x - 2) + abs (x + 1) = 3
      rintro (rfl | rfl | rfl | rfl)
      · -- x = -1
        norm_num
      · -- x = 0
        norm_num
      · -- x = 1
        norm_num
      · -- x = 2
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
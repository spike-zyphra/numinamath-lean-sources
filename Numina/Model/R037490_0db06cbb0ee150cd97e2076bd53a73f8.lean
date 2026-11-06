import Mathlib

theorem algebra_3699 :
  ∑ᶠ x ∈ {x : ℝ | abs (x - 16) + abs (x - 2) = 23}, x = 18 := by
  have h1 : {x : ℝ | abs (x - 16) + abs (x - 2) = 23} = {-2.5, 20.5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume abs (x - 16) + abs (x - 2) = 23, prove x ∈ {-2.5, 20.5}
      intro h
      by_cases h2 : x ≥ 16
      · -- x ≥ 16
        rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h
        have hx : x = 20.5 := by
          nlinarith
        rw [hx]
        norm_num
      by_cases h3 : x ≥ 2
      · -- 2 ≤ x < 16
        rw [abs_of_nonpos (by linarith), abs_of_nonneg (by linarith)] at h
        exfalso
        linarith
      · -- x < 2
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)] at h
        have hx : x = -2.5 := by
          nlinarith
        rw [hx]
        norm_num
    · -- Assume x ∈ {-2.5, 20.5}, prove abs (x - 16) + abs (x - 2) = 23
      rintro (h | h)
      · -- x = -2.5
        rw [h]
        norm_num [abs_of_nonpos, abs_of_nonneg, abs_of_nonpos, abs_of_nonneg]
      · -- x = 20.5
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonneg, abs_of_nonpos, abs_of_nonneg]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num
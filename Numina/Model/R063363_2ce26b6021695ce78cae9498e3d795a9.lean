import Mathlib

/- Let $x$ be an integer. If $\left| x-1 \right|+\left| x-3 \right| < 8$, find the sum of all possible values of $x$.

 -/
theorem inequalities_3383 :
    ∑ᶠ x ∈ {x : ℤ | abs (x - 1) + abs (x - 3) < 8}, x = 14 := by
  have h1 : {x : ℤ | abs (x - 1) + abs (x - 3) < 8} = {-1, 0, 1, 2, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if |x-1| + |x-3| < 8, then x ∈ {-1, 0, 1, 2, 3, 4, 5}
      intro h
      by_cases h1 : x ≥ 3
      · -- x ≥ 3
        rw [abs_of_nonneg (by omega), abs_of_nonneg (by omega)] at h
        omega
      · -- 1 ≤ x < 3
        by_cases h2 : x ≥ 1
        · -- 1 ≤ x < 3
          rw [abs_of_nonneg (by omega), abs_of_nonpos (by omega)] at h
          omega
        · -- x < 1
          rw [abs_of_nonpos (by omega), abs_of_nonpos (by omega)] at h
          omega
    · -- Backward direction: x ∈ {-1, 0, 1, 2, 3, 4, 5} implies |x-1| + |x-3| < 8
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = -1
        norm_num
      · -- x = 0
        norm_num
      · -- x = 1
        norm_num
      · -- x = 2
        norm_num
      · -- x = 3
        norm_num
      · -- x = 4
        norm_num
      · -- x = 5
        norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Finset.sum_insert, Finset.sum_singleton]
  <;> rfl
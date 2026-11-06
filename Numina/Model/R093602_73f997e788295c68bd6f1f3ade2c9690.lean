import Mathlib

theorem inequalities_3814 : {x : ℤ | 80 * x ^ 2 - 348 * x - 506 < 0}.encard = 7 := by
  have h1 : {x : ℤ | 80 * x ^ 2 - 348 * x - 506 < 0} = {-1, 0, 1, 2, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · intro h
      have h1 : 80 * x ^ 2 - 348 * x - 506 < 0 := h
      have h2 : x ≥ -1 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 5)]
      have h3 : x ≤ 5 := by nlinarith [sq_nonneg (x + 1), sq_nonneg (x - 5)]
      interval_cases x <;> tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl
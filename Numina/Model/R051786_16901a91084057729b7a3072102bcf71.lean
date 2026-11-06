import Mathlib

theorem inequalities_72155 : {n : ℤ | n^4 - n^3 - 3*n^2 - 3*n - 17 < 0}.encard = 4 := by
  have h1 : {n : ℤ | n^4 - n^3 - 3*n^2 - 3*n - 17 < 0} = {-1, 0, 1, 2} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h : n^4 - n^3 - 3n^2 - 3n - 17 < 0, prove n ∈ {-1, 0, 1, 2}
      intro h
      have h2 : n ≥ -1 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 2), sq_nonneg (n * (n - 2)), sq_nonneg ((n + 1) * (n - 2)), sq_nonneg (n * (n + 1)), sq_nonneg (n * (n - 2))]
      have h3 : n ≤ 2 := by
        nlinarith [sq_nonneg (n + 1), sq_nonneg (n - 2), sq_nonneg (n * (n - 2)), sq_nonneg ((n + 1) * (n - 2)), sq_nonneg (n * (n + 1)), sq_nonneg (n * (n - 2))]
      interval_cases n <;> tauto
    · -- Assume n ∈ {-1, 0, 1, 2}, prove n^4 - n^3 - 3n^2 - 3n - 17 < 0
      rintro (rfl | rfl | rfl | rfl)
      · -- n = -1
        norm_num
      · -- n = 0
        norm_num
      · -- n = 1
        norm_num
      · -- n = 2
        norm_num
  rw [h1]
  rw [Set.encard]
  norm_num [Set.ncard]
  <;> try { native_decide }
  all_goals
    try { native_decide }
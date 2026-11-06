import Mathlib

theorem inequalities_5849 : {n : ℤ | -50 < n ^ 3 ∧ n ^ 3 < 50}.encard = 7 := by 
  have h1 : {n : ℤ | -50 < n ^ 3 ∧ n ^ 3 < 50} = {-3, -2, -1, 0, 1, 2, 3} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume -50 < n^3 ∧ n^3 < 50, need to show n ∈ {-3, -2, -1, 0, 1, 2, 3}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n ≥ -3 := by 
        nlinarith [sq_nonneg (n + 4), sq_nonneg (n - 3), sq_nonneg (n ^ 2), sq_nonneg ((n + 4) * (n - 3)), sq_nonneg ((n + 4) ^ 2), sq_nonneg ((n - 3) ^ 2)]
      have h4 : n ≤ 3 := by
        nlinarith [sq_nonneg (n - 3), sq_nonneg (n + 4), sq_nonneg (n ^ 2), sq_nonneg ((n - 3) * (n + 4)), sq_nonneg ((n - 3) ^ 2), sq_nonneg ((n + 4) ^ 2)]
      interval_cases n <;> norm_num at h1 h2 ⊢ <;> tauto
    · -- Assume n ∈ {-3, -2, -1, 0, 1, 2, 3}, need to show -50 < n^3 ∧ n^3 < 50
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }
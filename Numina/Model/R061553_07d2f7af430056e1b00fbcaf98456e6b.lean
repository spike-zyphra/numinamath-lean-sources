import Mathlib

theorem algebra_11317 :
    Set.ncard {n : ℤ | 0 < n ∧ (n + 8) * (n - 3) * (n - 12) < 0} = 8 := by
  have h1 : {n : ℤ | 0 < n ∧ (n + 8) * (n - 3) * (n - 12) < 0} = {4, 5, 6, 7, 8, 9, 10, 11} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if n > 0 and (n + 8)(n - 3)(n - 12) < 0, then n ∈ {4, 5, 6, 7, 8, 9, 10, 11}
      intro h
      rcases h with ⟨hn_pos, h1⟩
      have h2 : n ≥ 4 := by
        nlinarith [h1, sq_nonneg (n - 4), sq_nonneg (n - 11), sq_nonneg (n - 3), sq_nonneg (n - 12)]
      have h3 : n ≤ 11 := by
        nlinarith [h1, sq_nonneg (n - 4), sq_nonneg (n - 11), sq_nonneg (n - 3), sq_nonneg (n - 12)]
      interval_cases n <;> tauto
    · -- Second direction: if n ∈ {4, 5, 6, 7, 8, 9, 10, 11}, then n > 0 and (n + 8)(n - 3)(n - 12) < 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num
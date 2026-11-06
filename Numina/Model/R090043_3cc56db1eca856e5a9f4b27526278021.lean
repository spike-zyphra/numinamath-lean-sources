import Mathlib

theorem algebra_12408 : {n : ℤ | -11 ≤ n ∧ n ≤ 11 ∧ (n - 2) * (n + 4) * (n + 8) < 0}.ncard = 8 := by
  have h1 : {n : ℤ | -11 ≤ n ∧ n ≤ 11 ∧ (n - 2) * (n + 4) * (n + 8) < 0} = {-11, -10, -9, -3, -2, -1, 0, 1} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · rintro ⟨h₁, h₂, h₃⟩
      interval_cases n <;> omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · omega
        all_goals
          constructor
          · omega
          · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }
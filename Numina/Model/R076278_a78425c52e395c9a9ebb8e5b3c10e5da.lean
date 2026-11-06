import Mathlib

theorem number_theory_272426 : {n | ∃ k, n = k^2 ∧ 1 ≤ k ∧ k ≤ 20 ∧ 9 ∣ n}.encard = 6 := by
  have : {n | ∃ k, n = k^2 ∧ 1 ≤ k ∧ k ≤ 20 ∧ 9 ∣ n} = {9, 36, 81, 144, 225, 324} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, prove that if $n \in$ LHS, then $n \in$ RHS
      rintro ⟨k, rfl, hk1, hk2, h9⟩
      have h3 : k ≤ 20 := by linarith
      interval_cases k <;> norm_num at *
      all_goals omega
    · -- Now prove the reverse direction, if $n \in$ RHS, then $n \in$ LHS
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 9
        use 3
        all_goals norm_num
      · -- n = 36
        use 6
        all_goals norm_num
      · -- n = 81
        use 9
        all_goals norm_num
      · -- n = 144
        use 12
        all_goals norm_num
      · -- n = 225
        use 15
        all_goals norm_num
      · -- n = 324
        use 18
        all_goals norm_num
  rw [this]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
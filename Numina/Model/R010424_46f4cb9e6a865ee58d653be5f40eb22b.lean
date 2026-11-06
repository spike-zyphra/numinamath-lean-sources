import Mathlib

theorem algebra_12993 :
    Set.ncard {a : ℤ | 0 < a ∧ 3 ∣ a ∧ a ∣ 12} = 3 := by
  have h : {a : ℤ | 0 < a ∧ 3 ∣ a ∧ a ∣ 12} = {3, 6, 12} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume a satisfies the conditions: 0 < a, 3 divides a, and a divides 12
      rintro ⟨ha_pos, ha_div_3, ha_dvd_12⟩
      have h1 : a ≤ 12 := by exact Int.le_of_dvd (by norm_num) ha_dvd_12
      interval_cases a <;> tauto
    · -- Show that the elements 3, 6, 12 satisfy the conditions
      rintro (rfl | rfl | rfl)
      · -- a = 3
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- a = 6
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- a = 12
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
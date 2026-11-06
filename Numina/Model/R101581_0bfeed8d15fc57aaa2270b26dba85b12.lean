import Mathlib

theorem number_theory_198149 : {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 7 ∣ x}.encard = 9 := by
  have h : {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 7 ∣ x} = 
    {21, 42, 63, 84, 105, 126, 147, 168, 189} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
        Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x in {x : ℕ | 1 ≤ x ∧ x ≤ 200 ∧ 3 ∣ x ∧ 7 ∣ x}
      intro h
      rcases h with ⟨h1, h2, h3, h4⟩
      interval_cases x <;> omega
    · -- Assume x in {21, 42, 63, 84, 105, 126, 147, 168, 189}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard_eq_toFinset_card']
  <;> try { native_decide }
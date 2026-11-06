import Mathlib

theorem number_theory_7773 : {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ 7 * x + 19 * y = 2012}.encard = 15 := by
  have h1 : {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ 7 * x + 19 * y = 2012} = 
      {282, 263, 244, 225, 206, 187, 168, 149, 130, 111, 92, 73, 54, 35, 16} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
              Set.union_insert, Set.union_singleton]
    constructor
    · -- First direction: if x in the left side, then in the right side
      rintro ⟨y, hx, hy, heq⟩
      have h2 : x ≤ 287 := by
        omega
      interval_cases x <;> try { 
        omega 
      }
    · -- Second direction: if x in the right side, then in the left side.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 282
        use 2
        all_goals norm_num
      · -- x = 263
        use 9
        all_goals norm_num
      · -- x = 244
        use 16
        all_goals norm_num
      · -- x = 225
        use 23
        all_goals norm_num
      · -- x = 206
        use 30
        all_goals norm_num
      · -- x = 187
        use 37
        all_goals norm_num
      · -- x = 168
        use 44
        all_goals norm_num
      · -- x = 149
        use 51
        all_goals norm_num
      · -- x = 130
        use 58
        all_goals norm_num
      · -- x = 111
        use 65
        all_goals norm_num
      · -- x = 92
        use 72
        all_goals norm_num
      · -- x = 73
        use 79
        all_goals norm_num
      · -- x = 54
        use 86
        all_goals norm_num
      · -- x = 35
        use 93
        all_goals norm_num
      · -- x = 16
        use 100
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
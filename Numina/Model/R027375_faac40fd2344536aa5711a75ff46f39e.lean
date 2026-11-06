import Mathlib


theorem number_theory_7783 :
    Set.ncard {x : ℕ | ∃ a b, Odd a ∧ Odd b ∧ a ∈ Finset.Icc 1 9 ∧ b ∈ Finset.Icc 1 9 ∧ x = a * b} = 14 := by

  have h1 : {x : ℕ | ∃ a b, Odd a ∧ Odd b ∧ a ∈ Finset.Icc 1 9 ∧ b ∈ Finset.Icc 1 9 ∧ x = a * b} = {1, 3, 5, 7, 9, 15, 21, 25, 27, 35, 45, 49, 63, 81} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Assume x ∈ {x : ℕ | ∃ a b, Odd a ∧ Odd b ∧ a ∈ Finset.Icc 1 9 ∧ b ∈ Finset.Icc 1 9 ∧ x = a * b}
      rintro ⟨a, b, hodd_a, hodd_b, ha, hb, hmul⟩

      have ha1 : a ≥ 1 := by
        simp [Finset.mem_Icc] at ha
        omega
      have ha2 : a ≤ 9 := by
        simp [Finset.mem_Icc] at ha
        omega

      have hb1 : b ≥ 1 := by
        simp [Finset.mem_Icc] at hb
        omega
      have hb2 : b ≤ 9 := by
        simp [Finset.mem_Icc] at hb
        omega

      interval_cases a <;> interval_cases b
      <;> norm_num [Nat.odd_iff] at hodd_a hodd_b
      <;> norm_num [hmul] at *
      <;> omega

    · -- Assume x ∈ {1, 3, 5, 7, 9, 15, 21, 25, 27, 35, 45, 49, 63, 81}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- 1 = 1 * 1
        use 1, 1
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 3 = 1 * 3
        use 1, 3
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 5 = 1 * 5
        use 1, 5
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 7 = 1 * 7
        use 1, 7
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 9 = 1 * 9
        use 1, 9
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 15 = 3 * 5
        use 3, 5
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 21 = 3 * 7
        use 3, 7
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 25 = 5 * 5
        use 5, 5
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 27 = 3 * 9
        use 3, 9
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 35 = 5 * 7
        use 5, 7
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 45 = 5 * 9
        use 5, 9
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 49 = 7 * 7
        use 7, 7
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 63 = 7 * 9
        use 7, 9
        all_goals try { norm_num [Nat.odd_iff] }
      · -- 81 = 9 * 9
        use 9, 9
        all_goals try { norm_num [Nat.odd_iff] }

  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide
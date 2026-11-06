import Mathlib

theorem algebra_103636 :
    Set.ncard {k : ℕ | ∃ x : ℤ, k * x - 12 = 3 * k} = 6 := by
  have h1 : {k : ℕ | ∃ x : ℤ, k * x - 12 = 3 * k} = {1, 2, 3, 4, 6, 12} := by
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward: if k in the set, then k in {1,2,3,4,6,12}
      intro hk
      rcases hk with ⟨x, hx⟩
      have h2 : (k : ℤ) * x = 3 * (k : ℤ) + 12 := by
        linarith
      have h3 : (k : ℤ) ∣ 12 := by
        use x - 3
        linarith
      have h4 : k ∣ 12 := by
        exact Int.ofNat_dvd_right.mp h3
      have h5 : k ≤ 12 := by
        exact Nat.le_of_dvd (by linarith) h4
      interval_cases k <;> try { omega }
    · -- Backward: if k in {1,2,3,4,6,12}, then k in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- k = 1
        use 15
        all_goals norm_num
      · -- k = 2
        use 9
        all_goals norm_num
      · -- k = 3
        use 7
        all_goals norm_num
      · -- k = 4
        use 6
        all_goals norm_num
      · -- k = 6
        use 5
        all_goals norm_num
      · -- k = 12
        use 4
        all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
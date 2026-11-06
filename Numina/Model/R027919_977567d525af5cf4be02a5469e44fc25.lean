import Mathlib

theorem number_theory_14286 :
    Set.ncard {n | ∃ k, n * k = 72 ∧ 5 < n ∧ n < 20} = 5 := by
  have h1 : {n | ∃ k, n * k = 72 ∧ 5 < n ∧ n < 20} = {6, 8, 9, 12, 18} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume that there exists a k such that n * k = 72 ∧ 5 < n ∧ n < 20
      rintro ⟨k, h_eq, h1, h2⟩
      have h3 : n ≤ 19 := by
        linarith
      interval_cases n <;> try { 
        omega
      }
    · -- Assume n is in the right side, so {6, 8, 9, 12, 18}, then possible to find k in left side.
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- n = 6
        use 12
        all_goals norm_num
      · -- n = 8
        use 9
        all_goals norm_num
      · -- n = 9
        use 8
        all_goals norm_num
      · -- n = 12
        use 6
        all_goals norm_num
      · -- n = 18
        use 4
        all_goals norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }
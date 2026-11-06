import Mathlib

theorem number_theory_231358 :
    Set.ncard {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ 20 * m + 18 * n = 2018} = 12 := by 
  have h1 : {m : ℕ | ∃ n : ℕ, 0 < m ∧ 0 < n ∧ 20 * m + 18 * n = 2018} = 
      {1, 10, 19, 28, 37, 46, 55, 64, 73, 82, 91, 100} := by
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume there exists n such that 0 < m and 0 < n 
      rintro ⟨n, hm, hn, h⟩
      have h1 : m ≤ 100 := by
        omega 
      interval_cases m <;> omega 
    · -- Assume m ∈ {1, 10, ..., 100}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show existence of n for m = 1
        use 111
        all_goals omega
      · -- Show existence of n for m = 10
        use 101
        all_goals omega
      · -- Show existence of n for m = 19
        use 91
        all_goals omega
      · -- Show existence of n for m = 28
        use 81
        all_goals omega
      · -- Show existence of n for m = 37
        use 71
        all_goals omega
      · -- Show existence of n for m = 46
        use 61
        all_goals omega
      · -- Show existence of n for m = 55
        use 51
        all_goals omega
      · -- Show existence of n for m = 64
        use 41
        all_goals omega
      · -- Show existence of n for m = 73
        use 31
        all_goals omega
      · -- Show existence of n for m = 82
        use 21
        all_goals omega
      · -- Show existence of n for m = 91
        use 11
        all_goals omega
      · -- Show existence of n for m = 100
        use 1
        all_goals omega
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
  <;> try { native_decide }
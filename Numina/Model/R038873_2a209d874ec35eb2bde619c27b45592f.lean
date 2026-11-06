import Mathlib

theorem number_theory_136261 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ x y z, n = 100 * x + 10 * y + z ∧ 1 ≤ x ∧ x < y ∧ y < z ∧
      ∃ k, n + (100 * y + 10 * z + x) + (100 * z + 10 * x + y) = k ∧ k ∈ Finset.Icc 100 999 ∧
      ∃ m, k = m * 111} ≤ 7 := by

  have h3 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ x y z, n = 100 * x + 10 * y + z ∧ 1 ≤ x ∧ x < y ∧ y < z ∧
      ∃ k, n + (100 * y + 10 * z + x) + (100 * z + 10 * x + y) = k ∧ k ∈ Finset.Icc 100 999 ∧
      ∃ m, k = m * 111} = {123, 124, 125, 134, 126, 135, 234} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: n is in the left side, prove it's in the right side
      intro h
      rcases h with ⟨⟨hn1, hn2⟩, x, y, z, heq, hx1, hxy, hyz, k, hk_eq, ⟨hk1, hk2⟩, m, hk_eq_m⟩
      have h4 : k = 111 * (x + y + z) := by
        nlinarith
      have h5 : m * 111 = 111 * (x + y + z) := by
        linarith [hk_eq_m, h4]
      have h6 : m = x + y + z := by
        omega
      have h7 : x + y + z ≤ 9 := by
        nlinarith
      have h8 : x + y + z ≥ 6 := by
        omega
      have h9 : x ≤ 9 := by 
        omega
      have h10 : y ≤ 9 := by 
        omega
      have h11 : z ≤ 9 := by 
        omega
      interval_cases x <;> try { 
        omega 
      } <;> try { 
        interval_cases y <;> try { 
          omega 
        } <;> try { 
          interval_cases z <;> omega 
        }
      }
    · -- Assume n is in the right side, prove it's in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 123
        exact ⟨by norm_num, 1, 2, 3, by norm_num, by norm_num, by norm_num, by norm_num, 666, by norm_num, by norm_num, 6, by norm_num⟩
      · -- n = 124
        exact ⟨by norm_num, 1, 2, 4, by norm_num, by norm_num, by norm_num, by norm_num, 777, by norm_num, by norm_num, 7, by norm_num⟩
      · -- n = 125
        exact ⟨by norm_num, 1, 2, 5, by norm_num, by norm_num, by norm_num, by norm_num, 888, by norm_num, by norm_num, 8, by norm_num⟩
      · -- n = 134
        exact ⟨by norm_num, 1, 3, 4, by norm_num, by norm_num, by norm_num, by norm_num, 888, by norm_num, by norm_num, 8, by norm_num⟩
      · -- n = 126
        exact ⟨by norm_num, 1, 2, 6, by norm_num, by norm_num, by norm_num, by norm_num, 999, by norm_num, by norm_num, 9, by norm_num⟩
      · -- n = 135
        exact ⟨by norm_num, 1, 3, 5, by norm_num, by norm_num, by norm_num, by norm_num, 999, by norm_num, by norm_num, 9, by norm_num⟩
      · -- n = 234
        exact ⟨by norm_num, 2, 3, 4, by norm_num, by norm_num, by norm_num, by norm_num, 999, by norm_num, by norm_num, 9, by norm_num⟩

  rw [h3]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
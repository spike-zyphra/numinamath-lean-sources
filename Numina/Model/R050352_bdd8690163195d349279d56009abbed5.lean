import Mathlib

theorem algebra_15535 : {n : ℕ | ∃ k, n = k^3 ∧ 100 ≤ n ∧ n ≤ 900}.encard = 5 := by
  have h1 : {n : ℕ | ∃ k, n = k^3 ∧ 100 ≤ n ∧ n ≤ 900} = {125, 216, 343, 512, 729} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Forward direction: if n is in the set, then n ∈ {125, 216, 343, 512, 729}
      rintro ⟨k, rfl, hk1, hk2⟩
      have h2 : k ≤ 9 := by
        by_contra h
        push_neg at h
        have h3 : k ≥ 10 := by omega
        have h4 : k^3 ≥ 1000 := by
          calc
            k^3 ≥ 10^3 := by apply Nat.pow_le_pow_of_le_left h3 3
            _ = 1000 := by norm_num
        linarith
      have h3 : k ≥ 5 := by
        by_contra h
        push_neg at h
        have h5 : k ≤ 4 := by omega
        have h6 : k^3 ≤ 64 := by
          have : k ≤ 4 := h5
          have h7 : k^3 ≤ (4 : ℕ) ^ 3 := by apply Nat.pow_le_pow_of_le_left h5 3
          have h8 : (4 : ℕ) ^ 3 = 64 := by norm_num
          linarith [h7, h8]
        linarith
      have hk : k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by
        omega
      rcases hk with (r | r | r | r | r)
      · -- k = 5
        subst k
        all_goals norm_num
      · -- k = 6
        subst k
        all_goals norm_num
      · -- k = 7
        subst k
        all_goals norm_num
      · -- k = 8
        subst k
        all_goals norm_num
      · -- k = 9
        subst k
        all_goals norm_num
    · -- Backward direction: if n ∈ {125, 216, 343, 512, 729}, then n is in the set
      rintro (r | r | r | r | r)
      · -- n = 125
        rw [r]
        use 5
        all_goals norm_num
      · -- n = 216
        rw [r]
        use 6
        all_goals norm_num
      · -- n = 343
        rw [r]
        use 7
        all_goals norm_num
      · -- n = 512
        rw [r]
        use 8
        all_goals norm_num
      · -- n = 729
        rw [r]
        use 9
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try rfl
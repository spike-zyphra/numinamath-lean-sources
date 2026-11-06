import Mathlib

theorem number_theory_214580 : {n : ℕ | n ≠ 0 ∧ ∃ k, n = k^2 ∧ ∃ m, n = m^3 ∧ n < 1000}.encard = 3 := by
  have h1 : {n : ℕ | n ≠ 0 ∧ ∃ k, n = k^2 ∧ ∃ m, n = m^3 ∧ n < 1000} = {1, 64, 729} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is in the left side
      rintro ⟨hn, k, rfl, m, hm₁, hk⟩
      have h2 : k ^ 2 < 1000 := by linarith
      have h3 : m ^ 3 < 1000 := by linarith
      have h4 : m ≤ 9 := by
        by_contra h
        push_neg at h
        have : m ^ 3 ≥ 1000 := by
          have h1 : m ≥ 10 := by linarith
          have h2 : m ^ 3 ≥ 1000 := by
            have h3 : m ^ 3 ≥ 10 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left
              linarith
            norm_num at h3 ⊢
            linarith
          linarith
        linarith
      interval_cases m <;> try { 
        have : k ≤ 31 := by nlinarith
        interval_cases k <;> omega -- minor fix needed
      }
      <;> tauto
      <;> omega
    · -- Assume n is in the right side
      rintro (rfl | rfl | rfl)
      · constructor
        · norm_num
        · use 1
          constructor
          · norm_num
          · use 1
            all_goals norm_num
      · constructor
        · norm_num
        · use 8
          constructor
          · norm_num
          · use 4
            all_goals norm_num
      · constructor
        · norm_num
        · use 27
          constructor
          · norm_num
          · use 9
            all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try rfl
  all_goals omega
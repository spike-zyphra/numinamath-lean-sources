import Mathlib

theorem number_theory_95626 :
    Set.ncard {n : ℕ | n > 0 ∧ ∃ k, n = k^3 ∧ n ∣ Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7} = 6 := by
  have h2 : {n : ℕ | n > 0 ∧ ∃ k, n = k^3 ∧ n ∣ Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7} = {1, 8, 27, 64, 216, 1728} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n in left
      intro hn
      rcases hn with ⟨hn_pos, k, rfl, hk⟩
      have h3 : k^3 ∣ Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7 := hk
      rw [show Nat.factorial 3 * Nat.factorial 5 * Nat.factorial 7 = 3628800 by native_decide] at h3
      have h4 : k ≤ 158 := by
        by_contra h
        push_neg at h
        have h5 : k > 158 := h
        have h6 : k^3 > 3628800 := by
          have h7 : k ≥ 159 := by omega
          have h8 : k^3 ≥ 159^3 := by
            have h9 : k ≥ 159 := h7
            have h10 : k^3 ≥ 159^3 := by 
              exact Nat.pow_le_pow_of_le_left h9 3
            linarith
          norm_num at h8 ⊢
          omega
        have h7 : k^3 ≤ 3628800 := by 
          exact Nat.le_of_dvd (by norm_num) h3
        linarith
      interval_cases k <;> norm_num at * <;> try tauto <;> norm_num
      <;> try native_decide 
    · -- Assume n in right
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · use 1
          all_goals norm_num
          <;> try native_decide
      · constructor
        · norm_num
        · use 2
          all_goals norm_num
          <;> try native_decide
      · constructor
        · norm_num
        · use 3
          all_goals norm_num
          <;> try native_decide
      · constructor
        · norm_num
        · use 4
          all_goals norm_num
          <;> try native_decide
      · constructor
        · norm_num
        · use 6
          all_goals norm_num
          <;> try native_decide
      · constructor
        · norm_num
        · use 12
          all_goals norm_num
          <;> try native_decide
  rw [h2]
  norm_num
  <;> try native_decide
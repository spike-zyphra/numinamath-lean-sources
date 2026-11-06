import Mathlib

theorem number_theory_236913 :
    Set.ncard {x : ℚ | ∃ n : ℕ, x = n / 15 ∧ 1 / 6 ≤ x ∧ x ≤ 1 / 3} = 3 := by
  have h1 : {x : ℚ | ∃ n : ℕ, x = n / 15 ∧ 1 / 6 ≤ x ∧ x ≤ 1 / 3} = {3 / 15, 4 / 15, 5 / 15} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the left side, need to show x is in the right.
      rintro ⟨n, rfl, h1, h2⟩
      have h3 : (n : ℚ) / 15 ≥ (1 / 6 : ℚ) := by linarith
      have h4 : (n : ℚ) / 15 ≤ (1 / 3 : ℚ) := by linarith
      have h5 : (n : ℚ) ≥ (2.5 : ℚ) := by
        have h6 : (n : ℚ) / 15 ≥ (1 / 6 : ℚ) := by linarith
        linarith
      have h6 : (n : ℚ) ≤ (5 : ℚ) := by
        have h7 : (n : ℚ) / 15 ≤ (1 / 3 : ℚ) := by linarith
        linarith
      have h7 : n ≥ 3 := by
        by_contra h8
        push_neg at h8
        have h8 : n ≤ 2 := by omega
        have h8' : (n : ℚ) ≤ (2 : ℚ) := by exact_mod_cast h8
        nlinarith
      have h8 : n ≤ 5 := by
        by_contra h9
        push_neg at h9
        have h9 : n ≥ 6 := by omega
        have h9' : (n : ℚ) ≥ (6 : ℚ) := by exact_mod_cast h9
        nlinarith
      interval_cases n <;> norm_num at *
    · -- Assume x is in the right side, need to show x is in the left.
      rintro (rfl | rfl | rfl)
      · -- Case x = 3/15
        use 3
        all_goals norm_num
      · -- Case x = 4/15
        use 4
        all_goals norm_num
      · -- Case x = 5/15
        use 5
        all_goals norm_num
  rw [h1]
  norm_num
  <;> try { tauto }
  all_goals norm_num
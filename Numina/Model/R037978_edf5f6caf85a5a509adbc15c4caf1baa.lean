import Mathlib

theorem number_theory_14350 :
    Set.ncard {x : ℕ | ∃ n, x = 2 ^ n ∧ x ∈ Finset.Icc 10 99} = 3 := by
  have h1 : {x : ℕ | ∃ n, x = 2 ^ n ∧ x ∈ Finset.Icc 10 99} = {16, 32, 64} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, prove that if x is in the left side, then it's in the right side.
      rintro ⟨n, rfl, hn₁, hn₂⟩
      have h2 : n ≥ 4 := by
        by_contra h
        push_neg at h
        have h3 : n ≤ 3 := by omega
        interval_cases n <;> norm_num at *
        <;> omega
      have h3 : n ≤ 6 := by
        by_contra h
        push_neg at h
        have h4 : n ≥ 7 := by omega
        have h5 : 2 ^ n ≥ 2 ^ 7 := by
          exact (Nat.pow_le_pow_of_le_right (by norm_num) h4)
        have h6 : 2 ^ 7 = 128 := by norm_num
        have h7 : 2 ^ n ≥ 128 := by linarith [h6, h5]
        nlinarith
      interval_cases n <;> norm_num at *
      <;> omega
    · -- Now the reverse direction
      rintro (rfl | rfl | rfl)
      · -- Show that 16 is in the left side
        use 4
        all_goals norm_num
      · -- Show that 32 is in the left side
        use 5
        all_goals norm_num
      · -- Show that 64 is in the left side
        use 6
        all_goals norm_num
  rw [h1]
  norm_num
  all_goals try tauto
  all_goals try nlinarith
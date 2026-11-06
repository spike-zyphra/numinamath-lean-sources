import Mathlib

theorem number_theory_7141 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ k, n = k^3 ∧ (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).toFinset.card = 3} = 4 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ ∃ k, n = k^3 ∧ (Nat.digits 10 n).length = 3 ∧
      (Nat.digits 10 n).toFinset.card = 3} = {125, 216, 512, 729} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Forward direction: If n is in the set, then n is in {125, 216, 512, 729}
      rintro ⟨⟨hn1, hn2⟩, ⟨k, rfl, hk1, hk2⟩⟩
      have hk3 : k ≤ 9 := by
        by_contra h
        push_neg at h
        have h3 : k ^ 3 ≥ 1000 := by
          have h4 : k ≥ 10 := by omega
          have h5 : k ^ 3 ≥ 10 ^ 3 := by
            apply Nat.pow_le_pow_of_le_left h4 3
          norm_num at h5 ⊢
          linarith
        linarith
      interval_cases k <;> norm_num at *
      <;> tauto
    · -- Backward direction: If n is in {125, 216, 512, 729}, then n is in the set
      rintro (rfl | rfl | rfl | rfl)
      · -- n = 125
        constructor
        · norm_num
        · use 5
          all_goals norm_num [Nat.digits, Nat.digitsAux]
      · -- n = 216
        constructor
        · norm_num
        · use 6
          all_goals norm_num [Nat.digits, Nat.digitsAux]
      · -- n = 512
        constructor
        · norm_num
        · use 8
          all_goals norm_num [Nat.digits, Nat.digitsAux]
      · -- n = 729
        constructor
        · norm_num
        · use 9
          all_goals norm_num [Nat.digits, Nat.digitsAux]
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
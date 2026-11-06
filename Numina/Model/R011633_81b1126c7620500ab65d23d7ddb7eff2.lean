import Mathlib

theorem number_theory_267740:
    {n: ℕ | ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p ^ 2 * q ^ 2 ∧ n < 1000}.encard = 7 := by
  have h1 : {n: ℕ | ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p < q ∧ n = p ^ 2 * q ^ 2 ∧ n < 1000} = 
    {36, 100, 196, 484, 676, 225, 441} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in the left side; prove in right.
      rintro ⟨p, q, hp, hq, hpq, hn, hn2⟩
      have h4 : p ≤ 31 := by
        by_contra h
        push_neg at h
        have h3 : p ≥ 32 := by linarith
        have h5 : p ^ 2 ≥ 1024 := by nlinarith
        have h8 : p ^ 2 * q ^ 2 ≥ 1024 := by
          have h9 : p ≥ 2 := Nat.Prime.two_le hp
          have h10 : q ^ 2 ≥ 1 := by nlinarith
          nlinarith
        nlinarith
      have h5 : q ≤ 31 := by
        by_contra h
        push_neg at h
        have h3 : q ≥ 32 := by linarith
        have h4 : p ≤ 31 := by
          omega
        have h5 : q ^ 2 ≥ 1024 := by nlinarith
        have h9 : p ≥ 2 := Nat.Prime.two_le hp 
        have h10 : p ^ 2 ≥ 4 := by nlinarith
        have h11 : p ^ 2 * q ^ 2 ≥ 4096 := by 
          nlinarith
        nlinarith
      interval_cases p <;> interval_cases q <;> norm_num at hp hq hn hn2 ⊢ <;> omega
    · -- Assume n is in the right side; prove in left.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n=36
        use 2, 3
        all_goals norm_num
      · -- n=100
        use 2, 5
        all_goals norm_num
      · -- n=196
        use 2, 7
        all_goals norm_num
      · -- n=484
        use 2, 11
        all_goals norm_num
      · -- n=676
        use 2, 13
        all_goals norm_num
      · -- n=225
        use 3, 5
        all_goals norm_num
      · -- n=441
        use 3, 7
        all_goals norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  all_goals aesop
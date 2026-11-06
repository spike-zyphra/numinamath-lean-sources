import Mathlib

theorem number_theory_5150 : {k : ℕ | ∃ n : ℕ, 1 < k ∧ n > 0 ∧ 2022 = ∑ i ∈ Finset.range k, (n + i)}.encard = 3 := by 
  have h1 : {k : ℕ | ∃ n : ℕ, 1 < k ∧ n > 0 ∧ 2022 = ∑ i ∈ Finset.range k, (n + i)} = {3, 4, 12} := by 
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor 
    · -- First direction.
      rintro ⟨n, hk1, hn, heq⟩ 
      have eq1 : ∀ k n : ℕ, ∑ i ∈ Finset.range k, (n + i) = k * n + k * (k - 1) / 2 := by
        intro k n
        induction k with
        | zero => 
          simp
        | succ k ih =>
          rw [Finset.sum_range_succ, ih] 
          cases k with
          | zero => 
            simp 
          | succ k => 
            simp [Nat.mul_add, Nat.add_mul, mul_comm k] at ih ⊢
            <;> ring_nf at ih ⊢
            <;> omega 
      have eq2 := eq1 k n
      rw [eq2] at heq 
      have h8 : k ≤ 63 := by 
        by_contra h 
        push_neg at h 
        have h6 : k ≥ 64 := by omega 
        have h9 : n ≥ 1 := by omega 
        have h7 : k * n + k * (k - 1) / 2 ≥ 2023 := by 
          have h10 : k * n ≥ 64 := by 
            nlinarith 
          have h11 : k * (k - 1) / 2 ≥ 2016 := by 
            have h12 : k - 1 ≥ 63 := by 
              omega 
            have h13 : k * (k - 1) ≥ 64 * 63 := by 
              nlinarith 
            have h14 : k * (k - 1) / 2 ≥ 64 * 63 / 2 := by 
              apply Nat.div_le_div_right 
              all_goals omega 
            omega 
          omega 
        omega 
      interval_cases k <;> try { 
        omega 
      } <;> try { 
          norm_num [Finset.sum_range_succ] at heq ⊢ 
          all_goals 
            omega 
        } 
    · -- Backward direction.
      rintro (rfl | rfl | rfl)
      · -- k = 3, n = 673
        use 673 
        all_goals
          native_decide 
      · -- k = 4, n = 504 
        use 504 
        all_goals
          native_decide 
      · -- k = 12, n = 163 
        use 163 
        all_goals 
          native_decide 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try tauto
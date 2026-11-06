import Mathlib

theorem number_theory_2970 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n.primeFactors.card = 5 ∧ ∃ k, n = k * (k + 1) * (k + 2) * (k + 3)} = 5 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 10000 99999 ∧ n.primeFactors.card = 5 ∧ ∃ k, n = k * (k + 1) * (k + 2) * (k + 3)} = 
    {17160, 24024, 32760, 43680, 57120} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      rintro ⟨⟨hn1, hn2⟩, hcard, ⟨k, rfl⟩⟩
      have hk1 : k ≤ 17 := by
        by_contra h
        push_neg at h
        have h4 : k * (k + 1) * (k + 2) * (k + 3) ≥ 18 * 19 * 20 * 21 := by
          have hk1 : k ≥ 18 := by linarith
          have hk2 : k + 1 ≥ 19 := by linarith
          have hk3 : k + 2 ≥ 20 := by linarith
          have hk4 : k + 3 ≥ 21 := by linarith
          have h1 : k * (k + 1) * (k + 2) * (k + 3) ≥ 18 * 19 * 20 * 21 := by
            apply Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (by linarith) hk2) hk3) hk4
          linarith
        norm_num at h4
        linarith
      interval_cases k <;> norm_num [Nat.primeFactors, Nat.primeFactorsList] at hcard ⊢
      <;> omega
    · -- Show the reverse direction: each of the numbers in the finite set satisfies the conditions
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        constructor
        · native_decide
        · use 10
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · native_decide
        · use 11
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · native_decide
        · use 12
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · native_decide
        · use 13
          all_goals norm_num
      · constructor
        · norm_num
        constructor
        · native_decide
        · use 14
          all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }
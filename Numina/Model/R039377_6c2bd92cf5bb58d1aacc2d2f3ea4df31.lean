import Mathlib

theorem number_theory_97639 :
    ∑ᶠ b ∈ {b : ℕ | 0 < b ∧ b < 1000 ∧ (∃ k, Nat.digits b (k ^ 2) = [6, 3]) ∧
      ∃ m, Nat.digits b (m ^ 3) = [7, 2]}, b = 371 := by 
  have h1 : {b : ℕ | 0 < b ∧ b < 1000 ∧ (∃ k, Nat.digits b (k ^ 2) = [6, 3]) ∧
      ∃ m, Nat.digits b (m ^ 3) = [7, 2]} = {10, 361} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume $b$ satisfies all the conditions, prove $b \in \{10, 361\}$ 
      rintro ⟨hb1, hb2, ⟨k, hk⟩, ⟨m, hm⟩⟩
      have h2 : k ^ 2 = 3 * b + 6 := by 
        have h3 : Nat.digits b (k ^ 2) = [6, 3] := hk
        have h4 : k ^ 2 = Nat.ofDigits b (Nat.digits b (k ^ 2)) := by 
          rw [Nat.ofDigits_digits]
        rw [h3] at h4
        simp [Nat.ofDigits, mul_add, mul_one] at h4 ⊢
        all_goals 
          omega
      have h3 : m ^ 3 = 2 * b + 7 := by 
        have h4 : Nat.digits b (m ^ 3) = [7, 2] := hm
        have h5 : m ^ 3 = Nat.ofDigits b (Nat.digits b (m ^ 3)) := by 
          rw [Nat.ofDigits_digits]
        rw [h4] at h5
        simp [Nat.ofDigits, mul_add, mul_one] at h5 ⊢
        all_goals 
          omega
      have h4 : b < 1000 := hb2
      have h5 : b > 0 := hb1
      have h6 : k ≤ 55 := by
        nlinarith
      have h7 : m ≤ 12 := by
        have h9 : m ^ 3 < 2007 := by
          nlinarith
        have h10 : m ≤ 12 := by
          by_contra h
          push_neg at h
          have h11 : m > 12 := by omega
          have h12 : m ≥ 13 := by omega
          have h13 : m ^ 3 ≥ 2197 := by
            have h14 : m ≥ 13 := h12
            have h15 : m ^ 3 ≥ 13 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left
              linarith
            nlinarith
          nlinarith
        linarith
      interval_cases m <;> try { 
        omega
      } <;> try { 
        interval_cases k <;> omega
      }
    · -- Assume b \in \{10, 361\}, prove that it satisfies all the conditions.
      rintro (rfl | rfl)
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · use 6
          native_decide
        · use 3
          native_decide
      · constructor
        · norm_num 
        constructor
        · norm_num 
        constructor
        · use 33
          native_decide
        · use 9
          native_decide
  rw [h1]
  rw [finsum_mem_pair]
  all_goals 
    norm_num
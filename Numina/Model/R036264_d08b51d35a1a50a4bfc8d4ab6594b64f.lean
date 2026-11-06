import Mathlib

theorem number_theory_608748 :
    ∃ S : Finset ℕ, {n : ℕ | ∃ a b c d : ℕ, 0 ≠ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ n = (a + b + c + d) ^ 3} = S ∧ S.sum (λ x => x) = 10745 := by
  have h1 : {n : ℕ | ∃ a b c d : ℕ, 0 ≠ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ n = (a + b + c + d) ^ 3} = {4913, 5832} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h: ∃ a b c d : ℕ, 0 ≠ a ∧ a ≤ 9 ∧ b ≤ 9 ∧ c ≤ 9 ∧ d ≤ 9 ∧ n = 1000 * a + 100 * b + 10 * c + d ∧ n = (a + b + c + d) ^ 3
      rintro ⟨a, b, c, d, ha1, ha2, hb2, hc2, hd2, hn1, hn2⟩
      have h3 : n = (a + b + c + d) ^ 3 := hn2
      rw [hn1] at h3
      have h4 : a + b + c + d ≤ 36 := by 
        omega 
      have h5 : a + b + c + d ≤ 21 := by
        by_contra h6
        push_neg at h6
        have h7 : (a + b + c + d: ℕ) ^ 3 ≥ (22: ℕ) ^ 3 := by 
          have h8 : (a + b + c + d: ℕ) ≥ 22 := by 
            omega
          have h9 : (a + b + c + d: ℕ) ^ 3 ≥ (22: ℕ) ^ 3 := by 
            apply Nat.pow_le_pow_of_le_left
            omega 
          linarith 
        have h8 : (a + b + c + d) ^ 3 ≤ 9999 := by
          have h9 : (a + b + c + d) ^ 3 = 1000 * a + 100 * b + 10 * c + d := by
            linarith [hn1, hn2]
          omega 
        nlinarith 
      interval_cases h : a + b + c + d <;> norm_num at h3 hn1 <;> omega 
    · -- Now prove the reverse implication
      rintro (rfl | rfl)
      · -- Show that 4913 is in the set
        refine' ⟨4, 9, 1, 3, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
      · -- Show that 5832 is in the set
        refine' ⟨5, 8, 3, 2, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩
  use {4913, 5832}
  constructor 
  · -- Show that {n | P n} = S
    rw [h1]
    ext n 
    simp 
  · -- Show that S.sum = 10745
    native_decide
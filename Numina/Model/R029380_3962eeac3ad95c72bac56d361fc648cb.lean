import Mathlib

theorem number_theory_205523 :
  {(A, B, C, D) : ℕ × ℕ × ℕ × ℕ | 
    A > 0 ∧ A ≤ 9 ∧ B ≤ 9 ∧ C ≤ 9 ∧ D ≤ 9 ∧
    A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D ∧
    ∃ n : ℕ, n^2 = Nat.ofDigits 10 [D, C, D, C, B, A, B, A]} =
  {(9, 7, 0, 4), (8, 0, 2, 1)} := by 
  ext ⟨A, B, C, D⟩
  simp [Nat.ofDigits, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- Forward implication: if (A, B, C, D) is in the set, then it's in the right side.
    intro h 
    rcases h with ⟨hA1, hA2, hB, hC, hD, hAneB, hAneC, hAneD, hBneC, hBneD, hCneD, ⟨n, hn⟩⟩
    have h8 : n ^ 2 = D + C * 10 + D * 100 + C * 1000 + B * 10000 + A * 100000 + B * 1000000 + A * 10000000 := by 
      norm_num [Nat.ofDigits] at hn ⊢ 
      all_goals 
      ring_nf at hn ⊢ 
      all_goals 
      omega
    have hn2 : n ^ 2 = 101 * ( (A * 10 + B) * 10000 + (C * 10 + D) ) := by
      ring_nf at h8 ⊢ 
      all_goals 
      omega
    have h9 : 101 ∣ n ^ 2 := by 
      omega 
    have h11 : 101 ∣ n := by 
      have h101 : Nat.Prime 101 := by
        norm_num 
      have h5 : 101 ∣ n ^ 2 := h9 
      have h7 : 101 ∣ n := by 
        apply Nat.Prime.dvd_of_dvd_pow 
        exact h101 
        exact h5 
      exact h7 
    rcases h11 with ⟨m, hm⟩ 
    have h10 : (101 * m) ^ 2 = 101 * ( (A * 10 + B) * 10000 + (C * 10 + D) ) := by 
      rw [show 101 * m = n by omega] 
      all_goals 
      linarith [hn2]
    have h11 : m ^ 2 = ( (A * 10 + B) * 10000 + (C * 10 + D) ) / 101 := by
      have h12 : (101 * m) ^ 2 = 101 * ( (A * 10 + B) * 10000 + (C * 10 + D) ) := h10 
      have h13 : (101 * m) ^ 2 = 101^2 * m^2 := by ring 
      rw [h13] at h12 
      have h14 : 101 * m^2 = ( (A * 10 + B) * 10000 + (C * 10 + D) ) := by 
        omega 
      have h15 : ( (A * 10 + B) * 10000 + (C * 10 + D) ) = 101 * m^2 := by 
        omega 
      have h16 : ( (A * 10 + B) * 10000 + (C * 10 + D) ) / 101 = m^2 := by 
        omega 
      all_goals 
      omega 
    have h21 : m ≤ 313 := by 
      nlinarith 
    have h22 : m ≥ 32 := by 
      nlinarith 
    interval_cases m <;> norm_num at h10 h11 <;> omega
  · -- Backward implication: if (A, B, C, D) is in the right side, then it's in the set.
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩)
    · -- Check that (9,7,0,4) is a valid quadruple
      constructor 
      · -- Show A > 0 
        norm_num 
      constructor 
      · -- Show A ≤ 9 
        norm_num 
      constructor 
      · -- Show B ≤ 9 
        norm_num 
      constructor 
      · -- Show C ≤ 9 
        norm_num 
      constructor 
      · -- Show D ≤ 9 
        norm_num 
      constructor 
      · -- Show A ≠ B 
        norm_num 
      constructor 
      · -- Show A ≠ C 
        norm_num 
      constructor 
      · -- Show A ≠ D 
        norm_num 
      constructor 
      · -- Show B ≠ C 
        norm_num 
      constructor 
      · -- Show B ≠ D 
        norm_num 
      constructor 
      · -- Show C ≠ D 
        norm_num 
      · -- Show existence of n 
        use 9898 
        all_goals 
          norm_num
    · -- Check that (8,0,2,1) is a valid quadruple
      constructor 
      · -- Show A > 0 
        norm_num 
      constructor 
      · -- Show A ≤ 9 
        norm_num 
      constructor 
      · -- Show B ≤ 9 
        norm_num 
      constructor 
      · -- Show C ≤ 9 
        norm_num 
      constructor 
      · -- Show D ≤ 9 
        norm_num 
      constructor 
      · -- Show A ≠ B 
        norm_num 
      constructor 
      · -- Show A ≠ C 
        norm_num 
      constructor 
      · -- Show A ≠ D 
        norm_num 
      constructor 
      · -- Show B ≠ C 
        norm_num 
      constructor 
      · -- Show B ≠ D 
        norm_num 
      constructor 
      · -- Show C ≠ D 
        norm_num 
      · -- Show existence of n 
        use 8989 
        all_goals 
          norm_num
import Mathlib

theorem number_theory_160963 (n : ℕ) :
    n ∈ {n | n ∈ Finset.Icc 100 999 ∧ (Nat.digits 10 n).prod = 120 ∧ ∃ m, (Nat.digits 10 n).sum = 2 ^ m} ↔
    n = 358 ∨ n = 385 ∨ n = 538 ∨ n = 583 ∨ n = 835 ∨ n = 853 := by
  rw [Set.mem_setOf_eq]
  constructor
  · -- Assume n in the set
    rintro ⟨hn, h1, ⟨m, h2⟩⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    have h3 : m ≤ 13 := by
      by_contra h
      push_neg at h
      have h5 : (2 : ℕ) ^ m ≥ (2 : ℕ) ^ 14 := by
        apply Nat.pow_le_pow_of_le_right 
        norm_num 
        omega 
      have h6 : (Nat.digits 10 n).sum ≤ 27 := by 
        interval_cases n <;> norm_num 
      have h7 : (2 : ℕ) ^ m ≤ 27 := by 
        linarith [h2, h6] 
      linarith [h5, h7]
    interval_cases n <;> norm_num at h1 h2 ⊢
    <;> interval_cases m <;> norm_num at h2 ⊢
    <;> omega 
  · -- Assume n is one of the listed numbers.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · -- If n = 358.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num 
    · -- If n = 385.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num 
    · -- If n = 538.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num 
    · -- If n = 583.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num 
    · -- If n = 835.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num 
    · -- If n = 853.
      constructor
      · norm_num 
      constructor
      · norm_num 
      · use 4
        all_goals norm_num
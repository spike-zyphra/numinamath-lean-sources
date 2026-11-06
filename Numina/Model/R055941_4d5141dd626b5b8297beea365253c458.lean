import Mathlib

theorem number_theory_14854 :
    Set.ncard {x : ℕ | x ∈ Finset.Icc 100 999 ∧ ∃ n, x = n^3 ∧ 9 ∣ x} = 2 := by
  have h : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ ∃ n, x = n^3 ∧ 9 ∣ x} = {216, 729} := by 
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor 
    · -- Assume x is a three-digit cube divisible by 9, show x is 216 or 729
      rintro ⟨⟨hx₁,hx₂⟩,n,hn₁,hn₂⟩
      have h1 : n ≥ 5 := by 
        by_contra h
        push_neg at h
        have h2 : n^3 < 100 := by
          interval_cases n <;> omega 
        linarith 
      have h2 : n ≤ 9 := by 
        by_contra h
        push_neg at h 
        have h3 : n^3 > 999 := by
          have h4 : n ≥ 10 := by linarith
          have h5 : n^3 ≥ 10^3 := by 
            have h6 : n ≥ 10 := by linarith 
            have h7 : n^3 ≥ 10^3 := by 
              apply Nat.pow_le_pow_of_le_left 
              omega 
            linarith 
          have h6 : 10^3 > 999 := by norm_num 
          linarith 
        linarith 
      interval_cases n <;> omega 
    · -- Show that 216 and 729 satisfy the conditions 
      rintro (rfl | rfl)
      · -- Case x = 216 
        constructor
        · norm_num 
        · -- 216 = 6^3 
          exact ⟨6, by norm_num, by norm_num⟩ 
      · -- Case x = 729 
        constructor
        · norm_num 
        · -- 729 = 9^3 
          exact ⟨9, by norm_num, by norm_num⟩ 
  rw [h]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> norm_num
import Mathlib

theorem number_theory_16027 : {x | x > 0 ∧ x ∣ 72 ∧ ∃ n, x = n^3}.encard = 2 := by 
  have h1 : {x | x > 0 ∧ x ∣ 72 ∧ ∃ n, x = n^3} = {1, 8} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, show that if x is in the left set, then x is in {1, 8}
      intro h
      rcases h with ⟨hx1, hx2, ⟨n, hxn⟩⟩
      rw [hxn]
      have hn1 : n^3 > 0 := by 
        nlinarith
      have hn2 : n^3 ∣ 72 := by 
        rw [show n^3 = x by linarith] 
        exact hx2
      have h2 : n ≤ 4 := by 
        by_contra h
        push_neg at h 
        have h3 : n ≥ 5 := by omega 
        have h4 : n^3 > 72 := by 
          have h5 : n ≥ 5 := by linarith 
          have h6 : n^3 ≥ 5^3 := by 
            have h7 : n ≥ 5 := by linarith 
            have h8 : (n : ℕ) ^ 3 ≥ (5 : ℕ) ^ 3 := by 
              apply Nat.pow_le_pow_of_le_left 
              all_goals linarith 
            linarith [h8] 
          nlinarith 
          all_goals linarith 
          all_goals nlinarith 
        have h72 : n^3 ≤ 72 := by 
          exact Nat.le_of_dvd (by norm_num) hn2 
        linarith 
      interval_cases n <;> norm_num at hn2 hn1 <;> tauto 
    · -- Show the reverse: if x is in {1, 8}, then x is in the left set 
      rintro (rfl | rfl)
      · -- x = 1 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · refine ⟨1, by norm_num⟩ 
      · -- x = 8 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · refine ⟨2, by norm_num⟩ 
  rw [h1] 
  rw [Set.encard]
  simp [Set.ncard_pair]
  all_goals norm_num 
  all_goals norm_num 
  all_goals norm_num 
  all_goals norm_num 
  all_goals norm_num 
  all_goals norm_num
import Mathlib

theorem number_theory_254005 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, (n + (10 * (n % 10) + (n / 10))) = k ^ 2} = 8 := by
  have : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ ∃ k, (n + (10 * (n % 10) + (n / 10))) = k ^ 2} = 
      {29, 38, 47, 56, 65, 74, 83, 92} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
        Set.mem_singleton_iff, and_imp]
    constructor 
    · -- Assume h
      rintro ⟨⟨hn1, hn2⟩, ⟨k, h⟩⟩
      interval_cases n <;> norm_num at h <;> try { 
        have : k ≤ 31 := by nlinarith 
        interval_cases k <;> omega
      }
    · -- Assume n ∈ {29, 38, 47, 56, 65, 74, 83, 92}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show n = 29 is in the set
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2
          use 11 
          all_goals norm_num 
      · -- Show n = 38 is in the set
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 47 is in the set
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 56 is in the set 
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 65 is in the set 
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 74 is in the set 
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 83 is in the set 
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
      · -- Show n = 92 is in the set 
        constructor 
        · -- Show n is in the range [10, 99]
          norm_num 
        · -- Show there exists k such that n + reverse(n) = k^2 
          use 11 
          all_goals norm_num 
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp
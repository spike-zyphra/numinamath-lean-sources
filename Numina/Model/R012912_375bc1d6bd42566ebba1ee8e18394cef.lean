import Mathlib

theorem number_theory_156762 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∃ k, n = k^2 ∧ (n % 100) = 25} = 7 := by 
  have : {n : ℕ | n ∈ Finset.Icc 1000 9999 ∧ ∃ k, n = k^2 ∧ (n % 100) = 25} = 
    {1225, 2025, 3025, 4225, 5625, 7225, 9025} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
      Set.mem_singleton_iff, and_imp]
    constructor
    · rintro ⟨⟨hn1, hn2⟩, ⟨k, h_n_eq_k2, h_n_mod_25⟩⟩
      have h1 : k ≤ 99 := by
        nlinarith
      have h2 : k ≥ 32 := by
        nlinarith
      interval_cases k <;> norm_num [h_n_eq_k2] at *
      <;> omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · use 35
          all_goals norm_num
      · constructor
        · norm_num
        · use 45
          all_goals norm_num
      · constructor
        · norm_num
        · use 55
          all_goals norm_num
      · constructor
        · norm_num
        · use 65
          all_goals norm_num
      · constructor
        · norm_num
        · use 75
          all_goals norm_num
      · constructor
        · norm_num
        · use 85
          all_goals norm_num
      · constructor
        · norm_num
        · use 95
          all_goals norm_num
  rw [this]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }
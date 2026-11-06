import Mathlib

theorem number_theory_199246 :
    ∑ᶠ P ∈ {P : ℕ | P.Prime ∧ (P + 2).Prime ∧ P * (P + 2) ≤ 2007}, P = 106 := by 
  have h1 : {P : ℕ | P.Prime ∧ (P + 2).Prime ∧ P * (P + 2) ≤ 2007} = {3, 5, 11, 17, 29, 41} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h, show P ∈ {3, 5, 11, 17, 29, 41}
      intro h
      rcases h with ⟨hP, hP2, hprod⟩
      have h2 : P ≤ 44 := by nlinarith
      interval_cases P <;> norm_num at hP hP2 hprod ⊢ <;> try { tauto }
      all_goals try { trivial }
    · -- Assume P ∈ {3, 5, 11, 17, 29, 41}, show h
      intro h
      rcases h with (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · native_decide 
        all_goals 
          constructor
          · native_decide 
          all_goals 
            try { trivial }
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  try { native_decide }
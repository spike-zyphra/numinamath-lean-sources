import Mathlib

theorem algebra_20881 :
    Set.ncard {x : ℕ | x > 0 ∧ x < 100 ∧ 4 ∣ x ∧ 6 ∣ x} = 8 := by 
  have h1 : {x : ℕ | x > 0 ∧ x < 100 ∧ 4 ∣ x ∧ 6 ∣ x} = {12, 24, 36, 48, 60, 72, 84, 96} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h
      rintro ⟨h1, h2, h3, h4⟩
      interval_cases n <;> norm_num at h1 h2 h3 h4 ⊢ <;> tauto
    · -- Assume h
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals 
        constructor 
        · norm_num
        all_goals 
          constructor 
          · norm_num
          all_goals 
            constructor 
            · norm_num 
            · norm_num
  rw [h1]
  have h2 : ( ({12, 24, 36, 48, 60, 72, 84, 96} : Set ℕ)).ncard = 8 := by
    have h2 : ( ({12, 24, 36, 48, 60, 72, 84, 96} : Set ℕ)) = 
      ↑({12, 24, 36, 48, 60, 72, 84, 96} : Finset ℕ) := by
      ext x
      simp
    rw [h2]
    rw [Set.ncard_coe_Finset]
    native_decide
  exact h2
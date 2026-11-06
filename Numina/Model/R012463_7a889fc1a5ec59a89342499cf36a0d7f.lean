import Mathlib

theorem number_theory_315672 : (Nat.card {p | p.Prime ∧ p ∈ Finset.Icc 1 100}) * 100 = 25 * 100 := by
  have h1 : Nat.card {p | p.Prime ∧ p ∈ Finset.Icc 1 100} = 25 := by
    have h2 : {p | p.Prime ∧ p ∈ Finset.Icc 1 100} = 
      {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} := by
      ext p
      simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, 
        Set.mem_singleton_iff, and_imp]
      constructor
      · -- Assume p is prime and in the range 1 ≤ p ≤ 100
        intro h
        rcases h with ⟨h_prime, ⟨h1, h100⟩⟩
        interval_cases p <;> norm_num at h_prime h1 h100 ⊢ <;> tauto
      · -- Show that each element in the explicit set is in the original set
        rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
        all_goals
          constructor
          · -- Show it's prime
            norm_num
          all_goals
            norm_num
    rw [h2]
    rw [Nat.card_eq_fintype_card]
    simp
  calc
    (Nat.card {p | p.Prime ∧ p ∈ Finset.Icc 1 100}) * 100 = 25 * 100 := by 
      rw [h1] 
    _ = 25 * 100 := by 
      rfl
import Mathlib

theorem number_theory_15266 :
    ((Nat.card {p : ℕ | p.Prime ∧ p < 12 ∧ 2 ∣ p}) * 100 : ℝ) / (Nat.card {p : ℕ | p.Prime ∧ p < 12}) = 20 := by
  have h1 : Nat.card {p : ℕ | p.Prime ∧ p < 12 ∧ 2 ∣ p} = 1 := by 
    have h2 : {p : ℕ | p.Prime ∧ p < 12 ∧ 2 ∣ p} = {2} := by 
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hp
        rcases hp with ⟨h1, h2, h3⟩
        interval_cases p <;> tauto
      · intro hp
        rw [hp]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
    rw [h2]
    simp
  have h2 : Nat.card {p : ℕ | p.Prime ∧ p < 12} = 5 := by 
    have h3 : {p : ℕ | p.Prime ∧ p < 12} = {2, 3, 5, 7, 11} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
        and_imp]
      constructor
      · intro hp
        rcases hp with ⟨h1, h2⟩
        interval_cases p <;> tauto
      · rintro (rfl | rfl | rfl | rfl | rfl)
        · constructor
          · norm_num
          · norm_num
        · constructor
          · norm_num
          · norm_num
        · constructor
          · norm_num
          · norm_num
        · constructor
          · norm_num
          · norm_num
        · constructor
          · norm_num
          · norm_num
    rw [h3]
    simp
  rw [h1, h2]
  norm_num
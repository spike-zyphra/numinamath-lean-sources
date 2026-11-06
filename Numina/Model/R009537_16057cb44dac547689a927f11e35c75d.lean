import Mathlib

theorem number_theory_16298 :
    Set.ncard {p : ℕ | p.Prime ∧ 30 < p ∧ p < 65 ∧ (p % 10).Prime} = 4 := by 
  have h1 : {p : ℕ | p.Prime ∧ 30 < p ∧ p < 65 ∧ (p % 10).Prime} = {37, 43, 47, 53} := by
    ext p 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- Assume p satisfies the conditions 
      intro hp
      rcases hp with ⟨h_prime, hp1, hp2, h_mod⟩
      interval_cases p <;> norm_num at h_prime hp1 hp2 h_mod <;> omega 
    · -- Assume p ∈ {37, 43, 47, 53}
      rintro (rfl | rfl | rfl | rfl)
      · -- p = 37
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.Prime]
      · -- p = 43
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.Prime]
      · -- p = 47
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.Prime]
      · -- p = 53
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        constructor 
        · norm_num 
        · norm_num [Nat.Prime]
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
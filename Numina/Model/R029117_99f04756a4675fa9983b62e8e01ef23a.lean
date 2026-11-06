import Mathlib

theorem algebra_12344 : {p : ℕ | p.Prime ∧ 30 < p ∧ p < 40}.encard = 2 := by
  have h1 : {p : ℕ | p.Prime ∧ 30 < p ∧ p < 40} = {31, 37} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First show that if p is in the set, then p is in {31, 37}
      intro hp
      rcases hp with ⟨h_prime, hp1, hp2⟩
      interval_cases p <;> norm_num at h_prime hp1 hp2 ⊢ <;> tauto
    · -- Now the reverse: if p is in {31, 37}, then p is in the set 
      rintro (rfl | rfl)
      · -- Check 31
        constructor
        · -- Is 31 prime?
          norm_num
        constructor 
        · norm_num 
        · norm_num 
      · -- Check 37
        constructor 
        · -- Is 37 prime?
          norm_num
        constructor 
        · norm_num 
        · norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_pair]
  <;> try { aesop }
import Mathlib

theorem number_theory_230737 : Set.Infinite {p | p.Prime ∧ ∃ k, p = 6 * k + 1} := by
  have h1 : {p | p.Prime ∧ ∃ k, p = 6 * k + 1} = {p | p.Prime ∧ p % 6 = 1} := by 
    ext p 
    simp only [Set.mem_setOf_eq] 
    constructor
    · -- Assume p in left side, prove right side 
      rintro ⟨h_prime, ⟨k, hk⟩⟩
      have : p % 6 = 1 := by
        omega 
      constructor
      · exact h_prime 
      · exact_mod_cast this 
    · -- Assume p in right side, prove left side 
      rintro ⟨h_prime, hp⟩ 
      have h2 : p % 6 = 1 := hp 
      refine ⟨h_prime, ?_⟩ 
      refine ⟨p / 6, by omega⟩ 
  rw [h1] 
  apply Nat.infinite_setOf_prime_modEq_one 
  all_goals norm_num
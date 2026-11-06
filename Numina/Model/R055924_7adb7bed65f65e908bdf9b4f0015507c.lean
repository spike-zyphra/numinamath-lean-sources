import Mathlib

theorem number_theory_102149 : {p : ℕ | p.Prime ∧ p < 100 ∧ p % 10 = 7}.encard = 6 := by 
  have h1 : {p : ℕ | p.Prime ∧ p < 100 ∧ p % 10 = 7} = {7, 17, 37, 47, 67, 97} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- If p is prime and less than 100 and ends with 7, then p is in our set
      intro hp
      rcases hp with ⟨h_prime, h_lt, h_mod⟩
      interval_cases p <;> norm_num at *
      all_goals tauto
    · -- Conversely, if p is in our set, then it's prime and less than 100
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num
        all_goals
          constructor
          · norm_num
          · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try native_decide
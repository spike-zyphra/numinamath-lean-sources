import Mathlib

theorem number_theory_150751 :
    {p : ℕ | p.Prime ∧ p < 100} =
    {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n is prime and n < 100, prove n is in the right side
    intro h
    rcases h with ⟨h_prime, h_lt⟩
    interval_cases n <;> tauto
  · -- Assume n is in the right side, prove n is prime and n < 100
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      constructor <;> norm_num
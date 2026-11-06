import Mathlib

theorem number_theory_7173 : {p : ℕ | p.Prime ∧ p < 100 ∧ (Nat.digits 10 p).length = 2 ∧ (Nat.digits 10 p)[1]! = 5}.encard = 2 := by
  have h1 : {p : ℕ | p.Prime ∧ p < 100 ∧ (Nat.digits 10 p).length = 2 ∧ (Nat.digits 10 p)[1]! = 5} = {53, 59} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume p in the left set, prove in the right
      rintro ⟨h_prime, h_lt, h_len, h_tens⟩
      interval_cases p <;> norm_num at h_prime h_lt h_len h_tens ⊢ <;> try tauto
    · -- Assume in {53, 59}, prove in the left side.
      rintro (rfl | rfl)
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
      · constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · native_decide
        · native_decide
  rw [h1]
  rw [Set.encard_pair (by norm_num)]
  all_goals try { norm_num }
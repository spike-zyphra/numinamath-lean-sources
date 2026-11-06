import Mathlib

theorem algebra_166202 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (10 * (n % 10) + (n / 10)) * 4 = 7 * n} = 4 := by

  have h1 : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (10 * (n % 10) + (n / 10)) * 4 = 7 * n} = {12, 24, 36, 48} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      rintro ⟨⟨hn1, hn2⟩, heq⟩
      interval_cases n <;> norm_num at heq <;> omega
    · -- Assume n is in {12, 24, 36, 48}
      rintro (rfl | rfl | rfl | rfl)
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
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { try { rfl } }
  <;> try { linarith }
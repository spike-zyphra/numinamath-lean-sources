import Mathlib

theorem algebra_14422 :
    Set.ncard {p : ℤ | p ∈ Finset.Icc 1 10 ∧ ∃ q : ℤ, p * q - 4 * p - 2 * q = 2} / 10 = (2 / 5 : ℚ) := by
  have h1 : {p : ℤ | p ∈ Finset.Icc 1 10 ∧ ∃ q : ℤ, p * q - 4 * p - 2 * q = 2} = {1, 3, 4, 7} := by
    ext p
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, prove if p in the set, then p ∈ {1, 3, 4, 7}
      intro h
      rcases h with ⟨⟨hp1, hp2⟩, ⟨q, h_eq⟩⟩
      interval_cases p <;> omega
    · -- Now, prove the reverse: if p ∈ {1,3,4,7}, then exists q
      rintro (rfl | rfl | rfl | rfl)
      · -- p = 1
        constructor
        · norm_num
        · use -6
          norm_num
      · -- p = 3
        constructor
        · norm_num
        · use 14
          norm_num
      · -- p = 4
        constructor
        · norm_num
        · use 9
          norm_num
      · -- p = 7
        constructor
        · norm_num
        · use 6
          norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  all_goals norm_num
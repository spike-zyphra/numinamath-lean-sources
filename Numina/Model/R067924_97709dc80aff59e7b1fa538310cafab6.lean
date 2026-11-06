import Mathlib

theorem number_theory_93502 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n % 6 = 2 ∧ n % 9 = 5 ∧ n % 11 = 7} = 5 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 100 999 ∧ n % 6 = 2 ∧ n % 9 = 5 ∧ n % 11 = 7} = {194, 392, 590, 788, 986} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in original set
      rintro ⟨⟨hn1, hn2⟩, hn3, hn4, hn5⟩
      interval_cases n <;> norm_num at hn1 hn2 hn3 hn4 hn5 <;> omega
    · -- Assume n in {194, 392, 590, 788, 986}, need to show n in original set
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- Check n = 194
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check n = 392
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check n = 590
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check n = 788
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Check n = 986
        constructor
        · norm_num
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num
import Mathlib

theorem number_theory_266735 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 24 29 ∧ ∃ x y, n = 5 * x + 8 * y} = 5 := by
  have h1 : {n : ℕ | n ∈ Finset.Icc 24 29 ∧ ∃ x y, n = 5 * x + 8 * y} = {24, 25, 26, 28, 29} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n is in {n | n ∈ Finset.Icc 24 29 ∧ ∃ x y, n = 5 * x + 8 * y}
      rintro ⟨⟨hn1, hn2⟩, ⟨x, y, hxy⟩⟩
      interval_cases n <;> omega
    · -- Assume n is in {24, 25, 26, 28, 29}
      rintro (rfl | rfl | rfl | rfl | rfl)
      · -- n = 24
        constructor
        · norm_num
        · use 0, 3
          all_goals norm_num
      · -- n = 25
        constructor
        · norm_num
        · use 5, 0
          all_goals norm_num
      · -- n = 26
        constructor
        · norm_num
        · use 2, 2
          all_goals norm_num
      · -- n = 28
        constructor
        · norm_num
        · use 4, 1
          all_goals norm_num
      · -- n = 29
        constructor
        · norm_num
        · use 1, 3
          all_goals norm_num
  rw [h1]
  norm_num
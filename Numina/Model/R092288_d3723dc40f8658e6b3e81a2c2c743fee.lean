import Mathlib

theorem number_theory_273639 :
    Set.ncard {x | x ≠ 0 ∧ 2016 % x = 7} = 4 := by
  have h1 : {x | x ≠ 0 ∧ 2016 % x = 7} = {41, 49, 287, 2009} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n ≠ 0 and 2016 % n = 7, prove n ∈ {41, 49, 287, 2009}
      intro h
      rcases h with ⟨hn₀, hn₁⟩
      have h2 : n ≤ 2016 := by
        by_contra h
        push_neg at h
        have h3 : 2016 % n = 2016 := by
          rw [Nat.mod_eq_of_lt]
          linarith
          all_goals linarith
        linarith
      interval_cases n <;> try { norm_num at hn₀ hn₁ ⊢ <;> omega }
    · -- Assume n ∈ {41, 49, 287, 2009}, prove n ≠ 0 and 2016 % n = 7
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
  all_goals norm_num
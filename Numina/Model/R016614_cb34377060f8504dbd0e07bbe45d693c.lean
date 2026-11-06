import Mathlib

theorem number_theory_3069 :
    ∑ᶠ a ∈ {a : ℤ | 0 < a ∧ a < 11 ∧ ∃ x y : ℤ, a * x + 21 * y = 11}, a = 1 + 2 + 4 + 5 + 8 + 10 := by
  have h1 : {a : ℤ | 0 < a ∧ a < 11 ∧ ∃ x y : ℤ, a * x + 21 * y = 11} = {1, 2, 4, 5, 8, 10} := by
    ext a
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- First, show that if a is in the set, then a ∈ {1, 2, 4, 5, 8, 10}.
      rintro ⟨ha_pos, ha_lt, ⟨x, y, heq⟩⟩
      have h2 : a > 0 := by linarith
      have h3 : a < 11 := by linarith
      interval_cases a <;> omega
    · -- Show that if a ∈ {1, 2, 4, 5, 8, 10}, then it's in the set.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- a = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x=11, y=0 as witnesses.
          use 11, 0
          all_goals norm_num
      · -- a = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x = -110, y = 11 as witnesses.
          use -110, 11
          all_goals norm_num
      · -- a = 4
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x = -55, y = 11 as witnesses.
          use -55, 11
          all_goals norm_num
      · -- a = 5
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x = -44, y = 11 as witnesses.
          use -44, 11
          all_goals norm_num
      · -- a = 8
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x = 88, y = -33 as witnesses.
          use 88, -33
          all_goals norm_num
      · -- a = 10
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Use x = -22, y = 11 as witnesses.
          use -22, 11
          all_goals norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
  <;> rfl
import Mathlib

theorem inequalities_184469 : {n : ℕ | 0 < n ∧ 2008 % n = 10}.encard = 11 := by

  have h1 : {n : ℕ | 0 < n ∧ 2008 % n = 10} = {18, 27, 37, 54, 74, 111, 222, 333, 666, 999, 1998} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in left side, prove in right side
      rintro ⟨hn_pos, h1⟩
      have h2 : n ≤ 2008 := by
        by_contra h
        push_neg at h
        have h3 : 2008 % n = 2008 := by
          rw [Nat.mod_eq_of_lt]
          all_goals linarith
        omega

      interval_cases n <;> norm_num at h1 ⊢
    · -- Assume n in right side, prove in left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 18
        constructor
        · norm_num
        · norm_num
      · -- n = 27
        constructor
        · norm_num
        · norm_num
      · -- n = 37
        constructor
        · norm_num
        · norm_num
      · -- n = 54
        constructor
        · norm_num
        · norm_num
      · -- n = 74
        constructor
        · norm_num
        · norm_num
      · -- n = 111
        constructor
        · norm_num
        · norm_num
      · -- n = 222
        constructor
        · norm_num
        · norm_num
      · -- n = 333
        constructor
        · norm_num
        · norm_num
      · -- n = 666
        constructor
        · norm_num
        · norm_num
      · -- n = 999
        constructor
        · norm_num
        · norm_num
      · -- n = 1998
        constructor
        · norm_num
        · norm_num

  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { native_decide }
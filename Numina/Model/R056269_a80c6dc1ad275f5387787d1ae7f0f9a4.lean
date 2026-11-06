import Mathlib

theorem number_theory_206213 : {N : ℕ | 2017 % N = 17}.encard = 13 := by
  have h1 : {N : ℕ | 2017 % N = 17} = {20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First prove if 2017 % n = 17, then n in the right side
      intro h
      have h1 : n ≤ 2017 := by
        by_contra h2
        push_neg at h2
        have h2 : 2017 % n = 2017 := by
          rw [Nat.mod_eq_of_lt]
          all_goals linarith  -- Solving the linear inequalities generated
        linarith  -- This will produce a contradiction with our hypothesis
      interval_cases n <;> norm_num at h ⊢
      <;> tauto  -- This handles the remaining trivial implications
    · -- Now prove the reverse direction: if n is in the right side, then 2017 % n = 17
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { rfl }
  <;> omega  -- To handle the trivial arithmetic
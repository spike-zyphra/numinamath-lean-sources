import Mathlib

theorem number_theory_258901 : {n | 2007 % n = 5} = {7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First direction: If 2007 % n = 5, then n is in the set
    intro h
    have h1 : n ≤ 2007 := by 
      by_contra h2
      push_neg at h2
      have h3 : 2007 % n = 2007 := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      omega
    interval_cases n <;> tauto
  · -- Second direction: If n is in the set, then 2007 % n = 5
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      norm_num
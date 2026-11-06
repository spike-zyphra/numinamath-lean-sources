import Mathlib

theorem number_theory_4230 :
  {n : ℕ | n ≠ 0 ∧ 83 % n = 2} = {3, 9, 27, 81} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First direction: if n ≠ 0 and 83 % n = 2, then n ∈ {3, 9, 27, 81}
    intro h
    rcases h with ⟨hn1, hn2⟩
    have h1 : n ≤ 83 := by
      by_contra h2
      push_neg at h2
      have h3 : 83 % n = 83 := by
        rw [Nat.mod_eq_of_lt]
        all_goals linarith
      linarith
    interval_cases n <;> norm_num at hn1 hn2 ⊢ <;> tauto
  · -- Second direction: if n ∈ {3, 9, 27, 81}, then n ≠ 0 ∧ 83 % n = 2
    rintro (rfl | rfl | rfl | rfl)
    · -- Case n = 3
      constructor
      · norm_num
      · norm_num
    · -- Case n = 9
      constructor
      · norm_num
      · norm_num
    · -- Case n = 27
      constructor
      · norm_num
      · norm_num
    · -- Case n = 81
      constructor
      · norm_num
      · norm_num
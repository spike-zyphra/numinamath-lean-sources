import Mathlib

theorem number_theory_273892 :
    {M : ℕ | 0 < M ∧ M < 10 ∧ 5 ∣ 1989 ^ M + M ^ 1889} = {1, 4} := by
  ext M
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- First, prove the forward direction: If M is in the set, then M = 1 or 4
    rintro ⟨h1, h2, h3⟩
    interval_cases M <;> norm_num at h3 ⊢
    <;> omega
  · -- Now the reverse direction: If M = 1 or 4, then in the set
    rintro (rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
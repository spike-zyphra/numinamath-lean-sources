import Mathlib

theorem number_theory_74970 :
    {(n : ℕ) | 0 < n ∧ (Nat.digits n 1998).length = 3 ∧ (Nat.digits n 1998).sum = 24} =
    {15, 22, 43} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Assume that n is in the set on the left side
    rintro ⟨hn_pos, h1, h2⟩
    have h3 : n ≤ 1998 := by
      by_contra h
      push_neg at h
      have h4 : n > 1998 := by linarith
      have h5 : (Nat.digits n 1998).length = 1 := by 
        simp [h4]
      omega -- contradiction between h5 and h1
    interval_cases n <;> norm_num at h1 h2 ⊢
    <;> omega
  · -- Assume that n is in the set on the right side
    rintro (rfl | rfl | rfl)
    · -- Show that 15 is in the left side
      constructor
      · norm_num
      constructor
      · native_decide
      · native_decide
    · -- Show that 22 is in the left side
      constructor
      · norm_num
      constructor
      · native_decide
      · native_decide
    · -- Show that 43 is in the left side
      constructor
      · norm_num
      constructor
      · native_decide
      · native_decide
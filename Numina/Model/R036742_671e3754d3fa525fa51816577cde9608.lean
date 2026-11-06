import Mathlib

theorem algebra_3178 :
  ∑ᶠ x ∈ {x : ℤ | ∃(a b c : ℤ), x = a + b + c ∧ |a-3| + |b+5| + |c-7| = 2}, x = 15 := by
  have h1 : {x : ℤ | ∃(a b c : ℤ), x = a + b + c ∧ |a-3| + |b+5| + |c-7| = 2} = {3, 5, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- First, show that if x ∈ {x : ℤ | ∃(a b c : ℤ), x = a + b + c ∧ |a-3| + |b+5| + |c-7| = 2}, then x ∈ {3, 5, 7}
      intro h
      rcases h with ⟨a, b, c, h_eq, h1⟩
      have h2 : a ≥ 1 := by
        cases' abs_le.mp (show |a - 3| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h3 h3
        linarith
      have h3 : a ≤ 5 := by
        cases' abs_le.mp (show |a - 3| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h4 h4
        linarith
      have h4 : b ≥ -7 := by
        cases' abs_le.mp (show |b + 5| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h5 h5
        linarith
      have h5 : b ≤ -3 := by
        cases' abs_le.mp (show |b + 5| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h6 h6
        linarith
      have h6 : c ≥ 5 := by
        cases' abs_le.mp (show |c - 7| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h7 h7
        linarith
      have h7 : c ≤ 9 := by
        cases' abs_le.mp (show |c - 7| ≤ 2 by linarith [abs_nonneg (a - 3), abs_nonneg (b + 5), abs_nonneg (c - 7), h1]) with h8 h8
        linarith
      interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num at h1 h_eq ⊢ <;> omega
    · -- Show that if x ∈ {3, 5, 7}, then x ∈ {x : ℤ | ∃(a b c : ℤ), x = a + b + c ∧ |a-3| + |b+5| + |c-7| = 2}
      rintro (rfl | rfl | rfl)
      · -- Case x = 3
        use 1, -5, 7
        all_goals norm_num
      · -- Case x = 5
        use 3, -6, 8
        all_goals norm_num
      · -- Case x = 7
        use 3, -5, 9
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  all_goals norm_num
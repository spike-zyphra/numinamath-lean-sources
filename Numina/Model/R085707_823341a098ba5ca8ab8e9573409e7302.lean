import Mathlib

theorem inequalities_6862 : {x : ℤ | x < 0 ∧ -98 ≤ 13 * x + 6 ∧ 13 * x + 6 ≤ 71}.encard = 8 := by
  have h1 : {x : ℤ | x < 0 ∧ -98 ≤ 13 * x + 6 ∧ 13 * x + 6 ≤ 71} = {-8, -7, -6, -5, -4, -3, -2, -1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in the left set, prove it's in the right set.
      rintro ⟨hx1, hx2, hx3⟩
      have h4 : x ≥ -8 := by
        omega
      have h5 : x ≤ -1 := by
        omega
      interval_cases x <;> tauto
    · -- Assume x in the right set, prove it's in the left set.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Verify -8 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -7 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -6 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -5 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -4 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -3 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -2 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- Verify -1 satisfies all the inequalities.
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl
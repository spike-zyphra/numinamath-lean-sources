import Mathlib

theorem inequalities_3975 :
    ∑ᶠ x ∈ {x : ℤ | |x^2 - 16 * x + 40| ≤ 20}, x = 80 := by
  have h1 : {x : ℤ | |x^2 - 16 * x + 40| ≤ 20} = {2, 3, 4, 5, 6, 10, 11, 12, 13, 14} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward direction: If |x² -16x +40| ≤ 20, then x ∈ {2, 3, 4, 5, 6, 10, 11, 12, 13, 14}
      intro h
      have h1 : -20 ≤ x^2 - 16 * x + 40 := by
        linarith [abs_le.mp h]
      have h2 : x^2 - 16 * x + 40 ≤ 20 := by
        linarith [abs_le.mp h]
      have h3 : x ≥ 2 := by 
        nlinarith [sq_nonneg (x - 10), sq_nonneg (x - 6)]
      have h4 : x ≤ 14 := by 
        nlinarith [sq_nonneg (x - 8), sq_nonneg (x - 8)]
      interval_cases x <;> tauto
    · -- Backward direction: If x ∈ {2, 3, 4, 5, 6, 10, 11, 12, 13, 14}, then |x² -16x +40| ≤ 20
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 2
        norm_num [abs_le]
      · -- x = 3
        norm_num [abs_le]
      · -- x = 4
        norm_num [abs_le]
      · -- x = 5
        norm_num [abs_le]
      · -- x = 6
        norm_num [abs_le]
      · -- x = 10
        norm_num [abs_le]
      · -- x = 11
        norm_num [abs_le]
      · -- x = 12
        norm_num [abs_le]
      · -- x = 13
        norm_num [abs_le]
      · -- x = 14
        norm_num [abs_le]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> native_decide
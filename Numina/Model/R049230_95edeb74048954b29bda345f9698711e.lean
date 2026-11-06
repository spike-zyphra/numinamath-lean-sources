import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_3371 :
  ∑ᶠ x ∈ {x : ℤ | 0 < x ∧ x ≠ 3 ∧ 3 * x + 6 + 1 / (x - 3) ≤ 1 / (x - 3) + 2 * x + 14}, x = 33 := by
  have h1 : {x : ℤ | 0 < x ∧ x ≠ 3 ∧ 3 * x + 6 + 1 / (x - 3) ≤ 1 / (x - 3) + 2 * x + 14} = {1, 2, 4, 5, 6, 7, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is in the original set.
      intro h
      rcases h with ⟨hx1, hx2, hineq⟩
      have h2 : x ≤ 8 := by
        by_contra h'
        push_neg at h'
        have h3 : x ≥ 9 := by omega
        have h4 : 3 * x + 6 + 1 / (x - 3) > 1 / (x - 3) + 2 * x + 14 := by
          have h5 : 1 / (x - 3) = 0 := by
            rw [Int.ediv_eq_zero_of_lt]
            omega
            all_goals omega
          rw [h5]
          omega
        linarith
      interval_cases x <;> norm_num at hineq ⊢ <;> tauto
    · -- Show that the elements of the finite set satisfy the original condition.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 4
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 5
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 6
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 7
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
      · -- x = 8
        constructor
        · norm_num
        constructor
        · norm_num
        · -- Check the inequality
          norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> rfl
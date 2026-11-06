import Mathlib

theorem inequalities_32034 :
    ∑ᶠ x ∈ {x : ℤ | 1 < (x - 2)^2 ∧ (x - 2)^2 < 25}, x = 12 := by
  have h1 : {x : ℤ | 1 < (x - 2)^2 ∧ (x - 2)^2 < 25} = {-2, -1, 0, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume 1 < (x - 2)^2 < 25, prove x ∈ {-2, -1, 0, 4, 5, 6}
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : x > -3 := by
        nlinarith [show (x - 2) ^ 2 < 25 from by nlinarith]
      have h4 : x < 7 := by
        nlinarith [show (x - 2) ^ 2 < 25 from by nlinarith]
      interval_cases x <;> tauto
    · -- Assume x ∈ {-2, -1, 0, 4, 5, 6}, prove 1 < (x - 2)^2 < 25
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = -2
        constructor
        · norm_num
        · norm_num
      · -- x = -1
        constructor
        · norm_num
        · norm_num
      · -- x = 0
        constructor
        · norm_num
        · norm_num
      · -- x = 4
        constructor
        · norm_num
        · norm_num
      · -- x = 5
        constructor
        · norm_num
        · norm_num
      · -- x = 6
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  <;> native_decide
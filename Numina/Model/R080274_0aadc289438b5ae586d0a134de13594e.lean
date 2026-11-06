import Mathlib
open Real
open scoped BigOperators

theorem inequalities_3137 :
  ∑ᶠ x ∈ {x : ℤ | 0 < x ∧ 3 * x - 7 < 13 ∧ -2 * x + 6 ≤ 7}, x = 21 := by
  have h1 : {x : ℤ | 0 < x ∧ 3 * x - 7 < 13 ∧ -2 * x + 6 ≤ 7} = {1, 2, 3, 4, 5, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      omega
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor <;> omega
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> rfl
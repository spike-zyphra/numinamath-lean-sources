import Mathlib

open Real
open scoped BigOperators

theorem inequalities_5531 : {x : ℤ | -28 ≤ 6 * x - 7 ∧ 6 * x - 7 ≤ 24}.ncard = 9 := by
  have h1 : {x : ℤ | -28 ≤ 6 * x - 7 ∧ 6 * x - 7 ≤ 24} = {-3, -2, -1, 0, 1, 2, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies the inequalities, prove x ∈ {-3, -2, -1, 0, 1, 2, 3, 4, 5}
      rintro ⟨h1, h2⟩
      omega
    · -- Assume x ∈ {-3, -2, -1, 0, 1, 2, 3, 4, 5}, prove x satisfies the inequalities
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = -3
        constructor <;> norm_num
      · -- x = -2
        constructor <;> norm_num
      · -- x = -1
        constructor <;> norm_num
      · -- x = 0
        constructor <;> norm_num
      · -- x = 1
        constructor <;> norm_num
      · -- x = 2
        constructor <;> norm_num
      · -- x = 3
        constructor <;> norm_num
      · -- x = 4
        constructor <;> norm_num
      · -- x = 5
        constructor <;> norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try native_decide
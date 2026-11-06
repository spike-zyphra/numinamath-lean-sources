import Mathlib

theorem inequalities_233451 : {x : ℤ | x - 1 < (x - 1)^2 ∧ (x - 1)^2 < 3 * x + 7}.encard = 4 := by
  have h1 : {x : ℤ | x - 1 < (x - 1)^2 ∧ (x - 1)^2 < 3 * x + 7} = {0, 3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies both inequalities
      rintro ⟨h1, h2⟩
      have h3 : x > -1 := by nlinarith
      have h4 : x < 6 := by nlinarith
      interval_cases x <;> tauto
    · -- Show that if x ∈ {0, 3, 4, 5}, then it satisfies both inequalities
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 0
        constructor <;> norm_num
      · -- x = 3
        constructor <;> norm_num
      · -- x = 4
        constructor <;> norm_num
      · -- x = 5
        constructor <;> norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide
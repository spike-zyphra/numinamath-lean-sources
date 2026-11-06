import Mathlib
open Real

theorem inequalities_6043 :
  Set.ncard {x : ℤ | -3 ≤ (3 * (x - 5) - 7) / 5 ∧ (3 * (x - 5) - 7) / 5 < 2} = 8 := by
  have h1 : {x : ℤ | -3 ≤ (3 * (x - 5) - 7) / 5 ∧ (3 * (x - 5) - 7) / 5 < 2} = {3, 4, 5, 6, 7, 8, 9, 10} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in the set, derive the bounds
      intro h
      rcases h with ⟨h₁, h₂⟩

      omega

    · -- Show that these elements satisfy the inequalities
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
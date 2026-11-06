import Mathlib

theorem inequalities_285399 : {x : ℤ | x ∈ Set.Icc (-5) 3 ∧ -3 * x^2 < -14}.encard = 4 := by
  have h1 : {x : ℤ | x ∈ Set.Icc (-5) 3 ∧ -3 * x^2 < -14} = {-5, -4, -3, 3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Assume x in original set
      rintro ⟨hx, hineq⟩
      rcases hx with ⟨h1, h2⟩
      interval_cases x <;> tauto
    · -- Assume x in explicit set
      rintro (rfl | rfl | rfl | rfl)
      · -- x = -5
        constructor
        · norm_num
        · norm_num
      · -- x = -4
        constructor
        · norm_num
        · norm_num
      · -- x = -3
        constructor
        · norm_num
        · norm_num
      · -- x = 3
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
import Mathlib

theorem algebra_11647 : {x : ℤ | -4 ≤ 2 * x + 1 ∧ 2 * x + 1 ≤ 6}.encard = 5 := by 
  have h1 : {x : ℤ | -4 ≤ 2 * x + 1 ∧ 2 * x + 1 ≤ 6} = {-2, -1, 0, 1, 2} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x satisfies -4 ≤ 2 * x + 1 ∧ 2 * x + 1 ≤ 6
      rintro ⟨h1, h2⟩
      omega
    · -- Assume x ∈ { -2, -1, 0, 1, 2 }
      rintro (rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl
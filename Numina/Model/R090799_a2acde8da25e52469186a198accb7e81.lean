import Mathlib

theorem inequalities_13410 : {x : ℕ | 0 < x ∧ x^2 < 165 - 4 * x}.encard = 10 := by
  have h1 : {x : ℕ | 0 < x ∧ x^2 < 165 - 4 * x} = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- forward direction: if x satisfies 0 < x and x^2 < 165 - 4*x, then x in the right set
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h1 : x ≤ 10 := by
        by_contra h
        push_neg at h
        have h2 : x ≥ 11 := by omega
        have : x^2 ≥ 121 := by nlinarith
        have : 165 - 4 * x ≤ 121 := by omega
        omega
      have h2 : x ≥ 1 := by linarith
      interval_cases x <;> norm_num at hx1 hx2 ⊢ <;> tauto
    · -- reverse direction: if x in the right set, then x satisfies 0 < x and x^2 < 165 - 4*x
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
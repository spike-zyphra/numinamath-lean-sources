import Mathlib

theorem algebra_20699 : {x : ℤ | 0 < x ∧ 3 * (x - 5) ≤ 7}.encard = 7 := by
  have h1 : {x : ℤ | 0 < x ∧ 3 * (x - 5) ≤ 7} = {1, 2, 3, 4, 5, 6, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the original set
      intro h
      rcases h with ⟨h_pos, h_ineq⟩
      omega
    · -- Assume x is in the finite set {1, 2, 3, 4, 5, 6, 7}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 1
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 2
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 3
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 4
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 5
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 6
        exact ⟨by norm_num, by norm_num⟩
      · -- x = 7
        exact ⟨by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
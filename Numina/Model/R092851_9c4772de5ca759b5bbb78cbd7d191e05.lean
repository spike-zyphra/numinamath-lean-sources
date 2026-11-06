import Mathlib

theorem algebra_286507 :
    {x : ℕ | x = 1 ∧ (20 / 100 : ℝ) * 40 = 8 ∨
      x = 2 ∧ 2^3 = 8 ∨
      x = 3 ∧ 7 - 3 * 2 = 8 ∨
      x = 4 ∧ 3^2 - 1^2 = 8 ∨
      x = 5 ∧ 2 * (6 - 4)^2 = 8}.encard = 4 := by
  have h1 : {x : ℕ | x = 1 ∧ (20 / 100 : ℝ) * 40 = 8 ∨
      x = 2 ∧ 2^3 = 8 ∨
      x = 3 ∧ 7 - 3 * 2 = 8 ∨
      x = 4 ∧ 3^2 - 1^2 = 8 ∨
      x = 5 ∧ 2 * (6 - 4)^2 = 8} = {1, 2, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if x is in the left set, prove it's in the right set
      rintro (h | h | h | h | h)
      · -- Case x = 1 ∧ (20 / 100 * 40 = 8)
        norm_num at h ⊢
        tauto
      · -- Case x = 2 ∧ 2^3 = 8
        norm_num at h ⊢
        tauto
      · -- Case x = 3 ∧ 7 - 3 * 2 = 8
        norm_num at h ⊢
        all_goals linarith
      · -- Case x = 4 ∧ 3^2 - 1^2 = 8
        norm_num at h ⊢
        tauto
      · -- Case x = 5 ∧ 2 * (6 - 4)^2 = 8
        norm_num at h ⊢
        tauto
    · -- Backward direction: if x is in the right set, prove it's in the left set
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        simp
        <;> norm_num
        <;> tauto
      · -- x = 2
        simp
        <;> norm_num
        <;> tauto
      · -- x = 4
        simp
        <;> norm_num
        <;> tauto
      · -- x = 5
        simp
        <;> norm_num
        <;> tauto
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { rfl }
  all_goals linarith
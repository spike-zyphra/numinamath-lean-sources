import Mathlib

theorem inequalities_5004 : {x : ℤ | x < 0 ∧ x^2 + 5 * x < 36}.encard = 8 := by
  have h1 : {x : ℤ | x < 0 ∧ x^2 + 5 * x < 36} = {-8, -7, -6, -5, -4, -3, -2, -1} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- Assume that $x$ is a negative integer satisfying $x^2 + 5x < 36$.
      intro h
      rcases h with ⟨h_neg, h_ineq⟩
      have h2 : x > -9 := by
        nlinarith [sq_nonneg (x + 9), sq_nonneg (x - 4)]
      interval_cases x <;> norm_num at h_ineq ⊢ <;> tauto
    · -- Assume that $x$ is in the finite set \{-8, -7, -6, -5, -4, -3, -2, -1\}, prove that it satisfies the inequality
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
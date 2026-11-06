import Mathlib

theorem algebra_9366 :
    {n : ℤ | n > 0 ∧ 2 * n - 5 < 5 - 2 * n} = {1, 2} := by 
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume n > 0 ∧ 2 * n - 5 < 5 - 2 * n, prove n = 1 ∨ n = 2
    intro h
    rcases h with ⟨h1, h2⟩
    have h3 : n < 3 := by 
      omega
    have h4 : n = 1 ∨ n = 2 := by 
      omega
    tauto
  · -- Assume n = 1 ∨ n = 2, prove n > 0 ∧ 2 * n - 5 < 5 - 2 * n
    rintro (rfl | rfl)
    · -- Case n = 1 
      constructor
      · norm_num
      · norm_num
    · -- Case n = 2 
      constructor
      · norm_num
      · norm_num
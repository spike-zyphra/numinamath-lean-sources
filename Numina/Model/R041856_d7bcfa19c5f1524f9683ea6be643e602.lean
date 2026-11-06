import Mathlib

theorem algebra_17027 :
    Set.ncard {n : ℤ | 10 < n ^ 2 ∧ n ^ 2 < 99} = 12 := by
  have : {n : ℤ | 10 < n ^ 2 ∧ n ^ 2 < 99} = {-9, -8, -7, -6, -5, -4, 4, 5, 6, 7, 8, 9} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n in {n : ℤ | 10 < n ^ 2 ∧ n ^ 2 < 99}, need to prove in the explicit set
      intro h
      rcases h with ⟨h1, h2⟩
      have h3 : n ≥ -9 := by 
        nlinarith
      have h4 : n ≤ 9 := by 
        nlinarith
      interval_cases n <;> tauto
    · -- Assume n in the explicit set, need to prove in {n | 10 < n ^ 2 ∧ n ^ 2 < 99}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = -9
        norm_num
      · -- n = -8
        norm_num
      · -- n = -7
        norm_num
      · -- n = -6
        norm_num
      · -- n = -5
        norm_num
      · -- n = -4
        norm_num
      · -- n = 4
        norm_num
      · -- n = 5
        norm_num
      · -- n = 6
        norm_num
      · -- n = 7
        norm_num
      · -- n = 8
        norm_num
      · -- n = 9
        norm_num
  rw [this]
  norm_num
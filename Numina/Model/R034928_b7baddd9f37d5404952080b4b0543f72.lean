import Mathlib

theorem number_theory_192829 :
    Set.ncard {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (1 / 4 : ℝ) * n = (Nat.digits 10 n).sum} = 4 := by
  have h : {n : ℕ | n ∈ Finset.Icc 10 99 ∧ (1 / 4 : ℝ) * n = (Nat.digits 10 n).sum} = {12, 24, 36, 48} := by
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h
      rintro ⟨⟨hn1, hn2⟩, hneq⟩
      interval_cases n <;> norm_num at hneq ⊢
      <;> tauto
    · -- Assume n ∈ {12, 24, 36, 48}
      rintro (rfl | rfl | rfl | rfl)
      · -- Case 12
        constructor
        · norm_num
        · norm_num
      · -- Case 24
        constructor
        · norm_num
        · norm_num
      · -- Case 36
        constructor
        · norm_num
        · norm_num
      · -- Case 48
        constructor
        · norm_num
        · norm_num
  rw [h]
  norm_num
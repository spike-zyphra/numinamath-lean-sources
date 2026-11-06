import Mathlib

theorem number_theory_192084 : {n : ℕ | (n ∈ Finset.Icc 100 999) ∧ ((n^2) % 10000 = 1001)} = {501, 749} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Forward implication: If n is in the set, then n is in {501, 749}
    rintro ⟨⟨hn1, hn2⟩, hsq⟩
    interval_cases n <;> norm_num at hsq ⊢ <;> omega
  · -- Backward implication: If n ∈ {501, 749}, then n is in the set
    rintro (rfl | rfl)
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
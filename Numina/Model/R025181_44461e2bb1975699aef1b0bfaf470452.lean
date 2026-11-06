import Mathlib

theorem number_theory_3891 (s : Set ℕ) (hs : s = {x : ℕ | x ∈ Finset.Icc 100 999 ∧ 3 * x % 5 = 4 ∧ 4 * x % 7 = 0 ∧ 5 * x % 11 = 6}) :
    ∑ᶠ x ∈ s, x = 483 + 868 := by
  rw [hs]
  have h1 : {x : ℕ | x ∈ Finset.Icc 100 999 ∧ 3 * x % 5 = 4 ∧ 4 * x % 7 = 0 ∧ 5 * x % 11 = 6} = {483, 868} := by
    ext x
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First direction: elements in the left side must be in {483, 868}
      rintro ⟨⟨h1, h2⟩, h3, h4, h5⟩
      interval_cases x <;> norm_num at h1 h2 h3 h4 h5 ⊢ <;> omega
    · -- Second direction: elements in {483, 868} must be in left side
      rintro (rfl | rfl)
      · -- Check 483
        native_decide
      · -- Check 868
        native_decide
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num
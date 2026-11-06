import Mathlib

theorem number_theory_609496 :
    {n : ℕ | n ∈ Finset.Icc 1 15 ∧ Nat.Prime (n ^ n + 1)} = {1, 2, 4} := by
  ext n
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- First, we show that if n is in the left side set, then n must be in {1,2,4}
    intro h
    rcases h with ⟨⟨hn1, hn2⟩, h3⟩
    interval_cases n <;> norm_num at h3 ⊢ <;> tauto
  · -- Now the reverse direction: if n is in {1,2,4}, then n is in the left side set.
    rintro (rfl | rfl | rfl)
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      · norm_num
import Mathlib

theorem number_theory_287259 :
    {n | n ∈ Finset.range 120 ∧ (n % 3 = 0 ∧ n % 4 = 0 ∧ n % 10 = 0)}.ncard = 2 ∧
    {n | n ∈ Finset.range 120 ∧ (n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0)}.ncard = 56 := by
  have h1 : {n | n ∈ Finset.range 120 ∧ (n % 3 = 0 ∧ n % 4 = 0 ∧ n % 10 = 0)} = {0, 60} := by
    ext n
    simp only [Finset.mem_range, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · rintro ⟨h1, ⟨h2, h3, h4⟩⟩
      omega
    · rintro (rfl | rfl)
      all_goals simp
  have h2 : {n | n ∈ Finset.range 120 ∧ (n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0)} = Finset.filter (λn ↦ n % 3 ≠ 0 ∧ n % 4 ≠ 0 ∧ n % 10 ≠ 0) (Finset.range 120) := by
    ext n
    simp
  rw [h1, h2, Set.ncard_coe_Finset]
  simp
  rw [Finset.filter, Finset.card]
  simp
  native_decide

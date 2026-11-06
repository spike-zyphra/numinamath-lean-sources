import Mathlib

theorem algebra_13893 : {C : ℕ | C < 10 ∧ 3 ∣ 100 + 10 * C + 3}.encard = 3 := by
  have h : {C : ℕ | C < 10 ∧ 3 ∣ 100 + 10 * C + 3} = {2, 5, 8} := by
    ext C
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      and_imp]
    constructor
    · -- Assume $C$ is in the set
      intro h
      rcases h with ⟨h1, h2⟩
      interval_cases C <;> norm_num at h2 ⊢ <;> tauto
    · -- Assume $C \in \{2, 5, 8\}$
      rintro (rfl | rfl | rfl)
      · constructor <;> norm_num
      · constructor <;> norm_num
      · constructor <;> norm_num
  rw [h]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { rfl }
  <;> try { trivial }
import Mathlib

theorem number_theory_15512 :
    Set.ncard {b : ℕ | 2 ≤ b ∧ (Nat.digits b 197).length = 4} = 2 := by
  have h1 : {b : ℕ | 2 ≤ b ∧ (Nat.digits b 197).length = 4} = {4, 5} := by
    ext b
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume $b \geq 2$ and the digit length of 197 in base $b$ is 4
      intro h
      rcases h with ⟨hb1, hb2⟩
      have h2 : b ≤ 197 := by
        by_contra h
        push_neg at h
        have h3 : (Nat.digits b 197).length = 1 := by
          simp [h]
          <;> omega
        omega
      interval_cases b <;> norm_num at hb1 hb2 ⊢ <;> tauto
    · -- Assume $b \in \{4, 5\}$
      rintro (rfl | rfl)
      · -- Case $b = 4$.
        constructor
        · norm_num  -- Show that 2 ≤ 4
        · norm_num  -- Show that the digit length of 197 in base 4 is 4.
      · -- Case $b = 5$.
        constructor
        · norm_num -- Show that 2 ≤ 5
        · norm_num -- Show that the digit length of 197 in base 5 is 4.
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
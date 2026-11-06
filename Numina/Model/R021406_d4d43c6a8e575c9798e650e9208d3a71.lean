import Mathlib

theorem number_theory_258725 :
    {x | ∃ n, x = n^3 ∧ x ∣ 9^4} = {1, 3^3, 3^6} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume $x \in \{x \mid \exists n, x = n^3 \wedge x \mid 9^4\}$, then $x \in \{1, 3^3, 3^6\}$
    rintro ⟨n, h1, h2⟩
    rw [h1] at h2
    have h3 : n^3 ∣ 9^4 := h2
    have h4 : n^3 ∣ 3^8 := by
      norm_num at h3 ⊢
      exact h3
    have h5 : n ^ 3 ∣ 3 ^ 8 := h4
    have h6 : n ≤ 18 := by
      by_contra h 
      push_neg at h 
      have h7 : n ^ 3 > 3 ^ 8 := by
        have h8 : n ≥ 19 := by 
          omega 
        have h9 : n ^ 3 ≥ 19 ^ 3 := by 
          have h10 : n ≥ 19 := h8 
          have h11 : n ^ 3 ≥ 19 ^ 3 := by 
            apply Nat.pow_le_pow_of_le_left 
            omega 
          linarith 
        norm_num at h9 ⊢ 
        linarith 
      have h8 : n ^ 3 ≤ 3 ^ 8 := by
        exact Nat.le_of_dvd (by norm_num) h5 
      linarith
    interval_cases n <;> norm_num [h1] at h5 ⊢
    <;> tauto
  · -- Assume $x \in \{1, 3^3, 3^6\}$, then $x \in \{x \mid \exists n, x = n^3 \wedge x \mid 9^4\}$
    rintro (h | h | h)
    · -- Suppose x = 1 
      rw [h]
      use 1
      all_goals norm_num 
    · -- Suppose x = 3^3 
      rw [h]
      use 3
      all_goals norm_num 
    · -- Suppose x = 3^6 
      rw [h]
      use 9 
      all_goals norm_num
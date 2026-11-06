import Mathlib

theorem algebra_10671 : {x : ℤ | x > 0 ∧ x^3 ≤ 200 ∧ x^3 ≥ 10}.encard = 3 := by
  have h1 : {x : ℤ | x > 0 ∧ x^3 ≤ 200 ∧ x^3 ≥ 10} = {3, 4, 5} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x > 0 ∧ x^3 ≤ 200 ∧ x^3 ≥ 10, show x ∈ {3, 4, 5}
      intro h
      rcases h with ⟨hx1, hx2, hx3⟩
      have h2 : x ≤ 5 := by
        by_contra h
        push_neg at h
        have h3 : x ^ 3 > 200 := by
          have h4 : x ≥ 6 := by omega
          have h5 : x ^ 3 ≥ 6 ^ 3 := by
            apply pow_le_pow_left
            all_goals linarith
          norm_num at h5 ⊢
          linarith
        linarith
      have h3 : x ≥ 3 := by
        by_contra h
        push_neg at h
        have h4 : x ≤ 2 := by omega
        have h5 : x ^ 3 < 10 := by
          by_cases h6 : x ≤ 2
          · 
            have h7 : x ^ 3 ≤ (2 : ℤ) ^ 3 := by
              apply pow_le_pow_left
              all_goals linarith
            norm_num at h7 ⊢
            linarith
          all_goals linarith
        linarith
      interval_cases x <;> tauto
    · -- Assume x ∈ {3, 4, 5}, show x > 0 ∧ x^3 ≤ 200 ∧ x^3 ≥ 10
      rintro (rfl | rfl | rfl)
      · -- x = 3
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 4
        exact ⟨by norm_num, by norm_num, by norm_num⟩
      · -- x = 5
        exact ⟨by norm_num, by norm_num, by norm_num⟩
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl
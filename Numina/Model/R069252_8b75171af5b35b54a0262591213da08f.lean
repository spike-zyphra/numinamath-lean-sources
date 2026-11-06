import Mathlib

theorem number_theory_5123 :
    ∑ᶠ x ∈ {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ x ^ 3 = y ^ 3 + y ^ 2 + y + 61}, x = 10 := by
  have h1 : {x : ℕ | ∃ y : ℕ, x > 0 ∧ y > 0 ∧ x ^ 3 = y ^ 3 + y ^ 2 + y + 61} = {4, 6} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x in the set, then there exists a positive y such that x^3 = y^3 + y^2 + y + 61
      rintro ⟨y, hx, hy, heq⟩
      have h2 : y ≤ 5 := by
        by_contra h
        push_neg at h
        have h1 : x > y := by
          have : x ^ 3 > y ^ 3 := by
            -- Rewrite the equation
            have h4 : x ^ 3 = y ^ 3 + y ^ 2 + y + 61 := heq
            nlinarith [show (y : ℕ) > 0 by linarith, show (x : ℕ) > 0 by linarith]
          have h2 : x > y := by
            by_contra h
            push_neg at h
            have : x ≤ y := by linarith
            have : x ^ 3 ≤ y ^ 3 := by
              apply Nat.pow_le_pow_of_le_left
              linarith
              all_goals linarith
            linarith
          exact h2
        have h4 : (y + 1) ^ 3 > x ^ 3 := by
          nlinarith [show (y : ℕ) >= 6 by omega, heq, show (x : ℕ) > 0 by linarith]
        have h6 : x < y + 1 := by
          by_contra h
          push_neg at h
          have h7 : x >= y + 1 := by omega
          have h8 : x ^ 3 >= (y + 1) ^ 3 := by
            apply Nat.pow_le_pow_of_le_left
            linarith
            all_goals linarith
          linarith
        omega
      interval_cases y <;> try { 
        norm_num at heq 
        all_goals 
        have hx1 : x ≤ 6 := by
          have h1 : x ^ 3 ≤ 216 := by
            norm_num at heq ⊢
            omega
          by_contra h
          push_neg at h
          have h3 : x ≥ 7 := by omega
          have h4 : x ^ 3 ≥ 343 := by
            have : x ≥ 7 := h3
            have h5 : x ^ 3 ≥ 7 ^ 3 := by
              apply Nat.pow_le_pow_of_le_left
              linarith
              all_goals linarith
            norm_num at h5 ⊢
            linarith
          linarith
        interval_cases x <;> omega 
      }
    · -- Show that both sides are imply each other
      rintro (rfl | rfl)
      · -- x = 4, then y = 1 is a solution
        use 1
        all_goals norm_num
      · -- x = 6, then y = 5 is a solution
        use 5
        all_goals norm_num
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num
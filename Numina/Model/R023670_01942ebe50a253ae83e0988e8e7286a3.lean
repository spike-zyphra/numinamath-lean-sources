import Mathlib

theorem algebra_310881 : ∑ᶠ x ∈ {x : ℕ | (x ^ 2 + 11) % (x + 1) = 0}, x = 22 := by 
  have h1 : {x : ℕ | (x ^ 2 + 11) % (x + 1) = 0} = {0, 1, 2, 3, 5, 11} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h : (x ^ 2 + 11) % (x + 1) = 0, show x ∈ {0, 1, 2, 3, 5, 11}
      intro h
      have h2 : x ≤ 11 := by
        by_contra h3
        push_neg at h3
        have h3 : x + 1 > 12 := by omega
        have h4 : (x + 1) ∣ (x ^ 2 + 11) := by
          exact Nat.dvd_of_mod_eq_zero h
        have h5 : (x + 1) ∣ 12 := by
          have h6 : (x + 1) ∣ (x ^ 2 + 11) := h4
          have h7 : (x + 1) ∣ ( (x + 1) * (x - 1) ) := by 
            simp
          have h8 : (x + 1) ∣ ( (x ^ 2 + 11) - ( (x + 1) * (x - 1) ) ) := by 
            apply Nat.dvd_sub' 
            · -- Show (x + 1) divides (x ^ 2 + 11)
              exact h6 
            · -- Show (x + 1) divides (x + 1) * (x - 1)
              exact h7 
          have h9 : ( (x ^ 2 + 11) - ( (x + 1) * (x - 1) ) ) = 12 := by 
            cases x with 
            | zero => 
              all_goals omega 
            | succ n => 
              cases n with 
              | zero => 
                all_goals omega 
              | succ n => 
                simp [Nat.mul_add, Nat.add_mul] at *
                <;> ring_nf 
                <;> omega 
          rw [h9] at h8 
          exact h8 
        -- If (x + 1) divides 12 and (x + 1) > 12, this is a contradiction.
        -- Since the largest divisor of 12 is 12.
        have h6 : (x + 1) ≤ 12 := by 
          exact Nat.le_of_dvd (by norm_num) h5 
        omega 
      interval_cases x <;> norm_num at h ⊢ 
    · -- Assume x in {0, 1, 2, 3, 5, 11}, show (x ^ 2 + 11) % (x + 1) = 0 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals 
        norm_num 
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  norm_num [Set.mem_insert_iff, Set.mem_singleton_iff]
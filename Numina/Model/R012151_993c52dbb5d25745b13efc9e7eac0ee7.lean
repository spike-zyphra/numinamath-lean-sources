import Mathlib

theorem number_theory_630163:
    ∑ᶠ x ∈ {n: ℕ | ∃ a b: ℕ, 0 < a ∧ 0 < b ∧ a + b = 156 ∧ n = a.gcd b}, x = 236 := by 
  have h1: {n: ℕ | ∃ a b: ℕ, 0 < a ∧ 0 < b ∧ a + b = 156 ∧ n = a.gcd b} = 
    {1,2,3,4,6,12,13,26,39,52,78} := by 
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
        Set.union_insert, Set.union_singleton]
    constructor 
    · -- First, show that if n is in the left side, it must be in the right side.
      intro h 
      rcases h with ⟨a, b, ha, hb, hsum, hn⟩
      have h2: n = a.gcd b := by 
        rw [hn]
      have h3: a.gcd b ∣ a := by 
        exact Nat.gcd_dvd_left a b 
      have h4: a.gcd b ∣ b := by 
        exact Nat.gcd_dvd_right a b 
      have h5: a.gcd b ∣ a + b := by 
        have h51: a.gcd b ∣ a := h3 
        have h52: a.gcd b ∣ b := h4 
        have h53: a.gcd b ∣ a + b := by 
          exact Nat.dvd_add h51 h52 
        exact h53 
      rw [show a + b = 156 by linarith] at h5 
      have h26: a.gcd b ∣ 156 := h5 
      have h211: a.gcd b ≤ 156 := by 
        exact Nat.le_of_dvd (show 0 < 156 by norm_num) h26 
      interval_cases h8 : a.gcd b <;> try { 
        simp [h2] at *
        all_goals 
          try { 
            omega 
          } 
      }
      <;> try { 
        tauto 
      }
    · -- Second, show the reverse direction.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl )
      · -- n = 1 
        use 1, 155
        all_goals norm_num [Nat.gcd]
      · -- n = 2 
        use 2, 154
        all_goals norm_num [Nat.gcd]
      · -- n = 3 
        use 3, 153
        all_goals norm_num [Nat.gcd]
      · -- n = 4 
        use 4, 152
        all_goals norm_num [Nat.gcd]
      · -- n = 6 
        use 6, 150
        all_goals norm_num [Nat.gcd]
      · -- n = 12 
        use 12, 144
        all_goals norm_num [Nat.gcd]
      · -- n = 13 
        use 13, 143
        all_goals norm_num [Nat.gcd]
      · -- n = 26 
        use 26, 130
        all_goals norm_num [Nat.gcd]
      · -- n = 39 
        use 39, 117
        all_goals norm_num [Nat.gcd]
      · -- n = 52 
        use 52, 104
        all_goals norm_num [Nat.gcd]
      · -- n = 78 
        use 78, 78
        all_goals norm_num [Nat.gcd]
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp
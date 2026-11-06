import Mathlib

theorem algebra_29621:
  ∑ᶠ (n : ℕ) (_ : n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24), n = 17 := by
  have h1 : {n : ℕ | n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24} = {2, 3, 12} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume h: n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24
      intro h
      rcases h with ⟨hn_pos, heq⟩
      have h4 : n ≤ 12 := by
        by_contra h
        push_neg at h
        have h5 : n ≥ 13 := by omega
        have h6 : n ^ 2 ∣ Nat.lcm (2 * n) (n ^ 2) := by
          apply Nat.dvd_lcm_right
        have h8 : Nat.lcm (2 * n) (n ^ 2) ≥ n ^ 2 := by
          have h10 : n ^ 2 ∣ Nat.lcm (2 * n) (n ^ 2) := h6
          have h11 : Nat.lcm (2 * n) (n ^ 2) > 0 := by
            have h12 : n > 0 := hn_pos
            have h13 : n ^ 2 > 0 := by
              nlinarith
            have h14 : Nat.lcm (2 * n) (n ^ 2) ≥ 1 := by
              apply Nat.lcm_pos
              all_goals linarith
            omega
          have h13 : n ^ 2 > 0 := by
            nlinarith
          have h12 : Nat.lcm (2 * n) (n ^ 2) ≥ n ^ 2 := by
            apply Nat.le_of_dvd (by omega) h10
            all_goals linarith
          linarith
        have h7 : 14 * n - 24 ≥ n ^ 2 := by
          have h8' : Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24 := by
            omega
          omega
        have h11 : n ^ 2 > 14 * n - 24 := by
          have h12 : n ≥ 13 := by omega
          have h13 : n ^ 2 > 14 * n - 24 := by
            have h14 : n ^ 2 + 24 > 14 * n := by
              nlinarith [show n ≥ 13 by omega]
            omega
          assumption
        omega
      interval_cases n <;> norm_num [Nat.lcm] at heq ⊢
      <;> tauto
    · -- Show that 2, 3, 12 satisfy
      rintro (rfl | rfl | rfl)
      · -- Show 2
        constructor
        · norm_num
        · -- Show lcm(4, 4) = 28 - 24 = 4
          norm_num [Nat.lcm]
      · -- Show 3
        constructor
        · norm_num
        · -- Show lcm(6, 9) = 42 - 24 = 18
          norm_num [Nat.lcm]
      · -- Show 12
        constructor
        · norm_num
        · -- Show lcm(24, 144) = 168 - 24 = 144
          norm_num [Nat.lcm]
  rw [show ∑ᶠ (n : ℕ) (hn : n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24), n = ∑ᶠ (n : ℕ) (hn : n ∈ {n : ℕ | n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24}), n by simp]
  rw [show ∑ᶠ (n : ℕ) (hn : n ∈ {n : ℕ | n > 0 ∧ Nat.lcm (2 * n) (n ^ 2) = 14 * n - 24}), n = ∑ᶠ (n : ℕ) (hn : n ∈ ({2, 3, 12} : Set ℕ)), n by rw [h1]]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try { native_decide }
  <;> try { tauto }
  all_goals try { omega }
  all_goals try { native_decide }
  all_goals try { tauto }
  all_goals try { native_decide }
  all_goals try { tauto }
  all_goals try { native_decide }
  all_goals try { tauto }
  all_goals try { native_decide }
  all_goals try { tauto }
  all_goals try { native_decide }
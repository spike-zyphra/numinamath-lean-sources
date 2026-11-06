import Mathlib

theorem number_theory_13088 : IsGreatest {n : ℕ+ | (10 ^ n.val / (2 ^ 5 * 5 ^ 8)) % 10 ^ n.val = 0} 7 := by
  constructor
  · -- Show that 7 is in the set.
    show ((10 ^ 7 / (2 ^ 5 * 5 ^ 8)) % 10 ^ 7 = 0)
    norm_num
  · -- Show that 7 is greatest in the set.
    intro n hn
    have h : (10 ^ n.val / (2 ^ 5 * 5 ^ 8)) % 10 ^ n.val = 0 := hn
    by_contra h'
    push_neg at h'
    have h8 : n.val ≥ 8 := by
      have : n.val ≥ 8 := by
        exact h'
      simpa using this
    have h1 : n.val ≥ 8 := h8
    have h2 : (10 ^ n.val / (2 ^ 5 * 5 ^ 8)) % 10 ^ n.val ≠ 0 := by
      have h3 : ∀ (m : ℕ), (10 ^ (8 + m) / (2 ^ 5 * 5 ^ 8)) % 10 ^ (8 + m) ≠ 0 := by
        intro m
        have h8 : (10 ^ (8 + m) / (2 ^ 5 * 5 ^ 8)) % 10 ^ (8 + m) ≠ 0 := by
          have h9 : ∀ (m : ℕ), (10 ^ (8 + m) / (2 ^ 5 * 5 ^ 8) : ℕ) = 8 * 10 ^ m := by
            intro m
            have h9 : 2 ^ 5 * 5 ^ 8 = 12500000 := by norm_num
            rw [h9]
            have h10 : ∀ (m : ℕ), (10 ^ (8 + m) : ℕ) / 12500000 = 8 * 10 ^ m := by
              intro m
              induction m with
              | zero => norm_num
              | succ m ih =>
                norm_num [Nat.pow_add, pow_one, pow_mul, mul_assoc] at ih ⊢
                all_goals
                omega
            specialize h10 m
            simpa using h10
          have h2 : (10 ^ (8 + m) / (2 ^ 5 * 5 ^ 8) : ℕ) = 8 * 10 ^ m := h9 m
          rw [h2]
          have hneq : (8 * 10 ^ m) % 10 ^ (8 + m) ≠ 0 := by
            have h10 : (8 * 10 ^ m) % 10 ^ (8 + m) ≠ 0 := by
              have h11 : (8 * 10 ^ m) % 10 ^ (8 + m) = 8 * 10 ^ m := by
                have h10 : 10 ^ (8 + m) > 8 * 10 ^ m := by
                  have h10' : 10 ^ 8 = 100000000 := by norm_num
                  have h5 : m ≥ 0 := by omega
                  have hmin : 10 ^ (8 + m) ≥ 10 ^ 8 := by
                    apply Nat.pow_le_pow_of_le_right
                    all_goals norm_num
                    all_goals omega
                  have hmax : 8 * 10 ^ m > 0 := by positivity
                  have h14 : 10 ^ (8 + m) > 8 * 10 ^ m := by
                    have h2 : 10 ^ (8 + m) = 10 ^ (8 + m) := rfl
                    have h3 : 8 * 10 ^ m < 10 ^ (8 + m) := by
                      have h4 : 8 * 10 ^ m < 10 ^ (8 + m) := by
                        have h5 : m < 8 + m := by omega
                        have h6 : (10: ℕ) ^ m ≥ 1 := by
                          apply Nat.one_le_pow
                          norm_num
                        have h7 : (10: ℕ) ^ (8 + m) = 10 ^ 8 * 10 ^ m := by
                          ring_nf
                        have h8 : 10 ^ 8 ≥ 100000000 := by
                          norm_num
                        have h9 : 8 * 10 ^ m > 0 := by positivity
                        have h10 : 10 ^ 8 > 8 := by
                          norm_num
                        have h11 : 10 ^ 8 * 10 ^ m > 8 * 10 ^ m := by
                          nlinarith
                        nlinarith
                      nlinarith
                    nlinarith
                  nlinarith
                have h2 : 8 * 10 ^ m < 10 ^ (8 + m) := h10
                have h3 : (8 * 10 ^ m) % 10 ^ (8 + m) = 8 * 10 ^ m := by
                  rw [Nat.mod_eq_of_lt]
                  all_goals nlinarith
                exact h3
              have : (8 * 10 ^ m) % 10 ^ (8 + m) = 8 * 10 ^ m := h11
              rw [this]
              have : 8 * 10 ^ m > 0 := by positivity
              have : 8 * 10 ^ m ≠ 0 := by positivity
              assumption
            assumption
          assumption
        exact h8
      have hk6 : ∀ (m : ℕ), (10 ^ (8 + m) / (2 ^ 5 * 5 ^ 8)) % 10 ^ (8 + m) ≠ 0 := h3
      have m : ∃ (m : ℕ), n.val = 8 + m := by
        refine ⟨n.val - 8, ?_⟩
        omega
      rcases m with ⟨m, hm⟩
      specialize hk6 m
      rw [show n.val = 8 + m by exact_mod_cast hm]
      exact_mod_cast hk6
    contradiction
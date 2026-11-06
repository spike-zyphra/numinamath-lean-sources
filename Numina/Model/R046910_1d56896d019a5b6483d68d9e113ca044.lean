import Mathlib

theorem number_theory_114731: {(a,n): ℕ×ℕ | 0 < a ∧ 0 < n ∧ 3^n = a^2 - 16} = {(5,2)} := by 
  ext ⟨a, n⟩
  simp 
  constructor
  · -- Assume that (a, n) is in the solution set 
    -- This means a > 0, n > 0, and 3^n = a^2 - 16
    rintro ⟨ha_pos, hn_pos, heq⟩ 
    have h1 : a^2 = 3^n + 16 := by 
      by_cases h2 : a^2 ≥ 16 
      · -- If $a^2 \ge 16$, then $a^2 - 16$ is the natural number difference.
        have h3 : a^2 = (a^2 - 16) + 16 := by 
          omega 
        have h4 : (a^2 - 16) = 3^n := by 
          omega 
        rw [h4] at h3 
        omega 
      · -- If $a^2 < 16$, then $a^2 - 16 = 0$ in natural numbers.
        have h3 : a^2 < 16 := by 
          omega 
        have h4 : (a^2 - 16 : ℕ) = 0 := by 
          omega 
        have h5 : 3^n = 0 := by 
          omega 
        have h5' : n = 0 := by 
          by_contra h 
          push_neg at h 
          have : n > 0 := by linarith 
          have h6 : 3^n > 0 := by 
            apply Nat.pow_pos 
            norm_num 
          linarith 
        linarith 
    by_cases h : n ≤ 2 
    · -- Assume n ≤ 2, so n = 1 or n = 2.
      interval_cases n <;> try { 
        all_goals 
        have h1' : a ≤ 8 := by 
          nlinarith 
        interval_cases a <;> omega 
      }
    · -- Assume n > 2. We want to show that (5, 2) is the only solution.
      have h2 : n > 2 := by 
        omega 
      by_cases h3 : n % 2 = 1 
      · -- Assume n is odd. We show a contradiction.
        have h4 : n % 2 = 1 := h3 
        have h5 : a^2 = 3^n + 16 := h1 
        have h6 : a ^ 2 % 4 = 0 ∨ a ^ 2 % 4 = 1 := by 
          have h1 : a % 4 = 0 ∨ a % 4 = 1 ∨ a % 4 = 2 ∨ a % 4 = 3 := by 
            omega 
          rcases h1 with (h1 | h1 | h1 | h1) <;> simp [Nat.pow_mod, h1]
        have h7 : (3 ^ n) % 4 = 3 := by 
          have h8 : ∀ k : ℕ, (3 ^ (2 * k + 1)) % 4 = 3 := by 
            intro k 
            induction k with 
            | zero => 
              norm_num 
            | succ k ih => 
              simp [Nat.pow_add, Nat.pow_mul] at ih ⊢ 
              all_goals 
              omega 
          have h9 : ∃ k : ℕ, n = 2 * k + 1 := by 
            refine' ⟨n / 2, by 
              omega 
            ⟩ 
          rcases h9 with ⟨k, hk⟩ 
          rw [show n = 2 * k + 1 by omega] 
          apply h8 k 
        have h8 : (3 ^ n + 16) % 4 = 3 := by 
          omega 
        have h9 : a ^ 2 % 4 = 3 := by 
          omega 
        omega 
      · -- Assume n is even. We show a contradiction.
        have h4' : n % 2 = 0 := by 
          omega 
        have h5 : a^2 = 3^n + 16 := h1 
        have h6 : ∃ k : ℕ, n = 2 * k := by 
          refine' ⟨n / 2, by 
            omega 
          ⟩ 
        rcases h6 with ⟨k, hk_eq⟩ 
        have h7k : k ≥ 2 := by
          omega 
        have h70 : a^2 = 3 ^ (2 * k) + 16 := by 
          rw [show n = 2 * k by linarith] at h5 
          all_goals 
          exact h5 
        have h8 : a^2 = (3^k)^2 + 16 := by 
          rw [h70] 
          ring_nf 
        by_cases h10 : k > 2 
        · -- Assume k > 2, so k ≥ 3 
          have h11 : k ≥ 3 := by 
            omega 
          have h9k : (3: ℕ) ^ k ≥ (27: ℕ) := by
            have h13 : k ≥ 3 := h11 
            have h5 : (3: ℕ) ^ k ≥ (3: ℕ) ^ 3 := by 
              apply Nat.pow_le_pow_of_le_right 
              all_goals 
                nlinarith 
            norm_num at h5 ⊢ 
            linarith 
          have h9 : a > 3^k := by
            nlinarith [show (3: ℕ) ^ k ≥ 9 by
              have h13 : k ≥ 2 := by 
                omega 
              have h14 : k ≥ 2 := h13 
              have h5 : (3: ℕ) ^ k ≥ (3: ℕ) ^ 2 := by 
                apply Nat.pow_le_pow_of_le_right 
                all_goals 
                  nlinarith 
              norm_num at h5 ⊢ 
              linarith
            ]
          have h9f : (a - 3^k) * (a + 3^k) = 16 := by 
            have h11f : a^2 = (3^k)^2 + 16 := h8 
            nlinarith [sq_nonneg (a - (3^k) : ℤ), sq_nonneg (a : ℤ), sq_nonneg ((3^k) : ℤ)]
          have h13f : (a - 3^k) ∣ 16 := by 
            use (a + 3^k)
            all_goals 
            linarith 
          have h14f : (a - 3^k) ≤ 16 := by 
            exact Nat.le_of_dvd (by norm_num) h13f 
          interval_cases h2 : (a - 3^k) <;> try { 
            omega 
          }
        · -- Assume k ≤ 2, so k = 2 
          have h12 : k = 2 := by 
            omega 
          rw [h12] at h8 
          have h13 : a ≤ 10 := by 
            nlinarith 
          interval_cases a <;> omega 
  · -- Show that (5, 2) is in the solution set 
    rintro ⟨rfl, rfl⟩ 
    constructor 
    · norm_num 
    constructor 
    · norm_num 
    · -- Show that 3^2 = 5^2 - 16 
      norm_num
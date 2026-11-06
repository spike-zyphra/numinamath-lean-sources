import Mathlib


theorem number_theory_132342 (a b : ℕ) : 2 * a ^ b = a * b + 3 ↔ a = 3 ∧ b = 1 := by
  constructor
  · -- Assume $2a^b = ab + 3$, prove $a = 3 ∧ b = 1$
    intro h
    have h1 : b ≤ 1 := by
      by_contra h2
      push_neg at h2
      have h2 : b ≥ 2 := by omega
      by_cases ha : a ≥ 2
      · -- a ≥ 2
        have h2a : 2 * a ^ b > a * b + 3 := by
          have h3 : ∀ (b : ℕ), b ≥ 2 → 2 * a ^ b > a * b + 3 := by
            intro b hb
            have h4 : b ≥ 2 := hb
            have base2 : 2 * a ^ 2 > a * 2 + 3 := by
              nlinarith [sq_nonneg (a - 1 : ℕ), sq_pos_of_pos (show 0 < (a : ℕ) by omega)]
            have step2 : ∀ (k : ℕ), k ≥ 2 → 2 * a ^ k > a * k + 3 → 2 * a ^ (k + 1) > a * (k + 1) + 3 := by
              intro k hk h
              have h6 : a ^ (k + 1) = a ^ k * a := by ring
              rw [h6] at *
              nlinarith [sq_nonneg (a - 1 : ℕ), h, mul_nonneg (show 0 ≤ (a : ℕ) by omega) (show 0 ≤ (a : ℕ) by omega)]
            exact Nat.le_induction base2 step2 b h4
          specialize h3 b (by omega)
          linarith
        nlinarith
      · -- a < 2
        have ha0 : a = 0 ∨ a = 1 := by omega
        rcases ha0 with (r | r)
        · -- a = 0
          rw [r] at h
          have h3 : 0 ^ b = 0 := by
            have hb1 : b ≥ 1 := by omega
            have h0 : ∀ (n : ℕ), 0 ^ (n + 1) = 0 := by
              intro n
              induction n with
              | zero => 
                norm_num
              | succ n ih =>
                simp [Nat.pow_add, Nat.mul_zero] at ih ⊢
            have hb11 : ∃ n, b = n + 1 := by 
              refine ⟨b - 1, by omega⟩
            rcases hb11 with ⟨n, hn⟩
            rw [hn]
            apply h0 n
          nlinarith [h3]
        · -- a = 1
          rw [r] at h
          have h3 : 1 ^ b = 1 := by
            have h4 : ∀ (n : ℕ), 1 ^ n = 1 := by
              intro n
              induction n with
              | zero => 
                norm_num
              | succ n ih =>
                simp [Nat.pow_succ] at ih ⊢
            specialize h4 b
            linarith
          nlinarith [h3]
    have h1 : b ≤ 1 := h1
    have hb01 : b = 0 ∨ b = 1 := by omega
    rcases hb01 with (r | r)
    · -- b = 0
      rw [r] at h
      exfalso
      norm_num at h
    · -- b = 1
      rw [r] at h
      have ha3 : a = 3 := by
        nlinarith
      constructor
      · linarith
      · linarith
  · -- Assume a = 3 ∧ b = 1, prove 2a^b = ab + 3
    rintro ⟨ha, hb⟩
    rw [ha, hb]
    all_goals norm_num
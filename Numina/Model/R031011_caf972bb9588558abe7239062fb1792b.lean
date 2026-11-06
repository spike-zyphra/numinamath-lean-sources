import Mathlib

theorem inequalities_146386 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (n : ℕ) (hn : 2 ≤ n) :
    (a ^ n + b ^ n) / 2 ≥ ((a + b) / 2) ^ n := by
  have h1 : (a ^ n + b ^ n) / 2 ≥ ((a + b) / 2) ^ n := by
    have h2 : a ^ n + b ^ n ≥ 2 * ((a + b) / 2) ^ n := by
      have base2 : a ^ 2 + b ^ 2 ≥ 2 * ((a + b) / 2) ^ 2 := by
        nlinarith [sq_nonneg (a - b)]
      have step2 : ∀ k : ℕ, k ≥ 2 →
        a ^ k + b ^ k ≥ 2 * ((a + b) / 2) ^ k →
        a ^ (k + 1) + b ^ (k + 1) ≥ 2 * ((a + b) / 2) ^ (k + 1) := by
        intro k hk ih
        have h50 : a ^ (k + 1) + b ^ (k + 1) = a * a ^ k + b * b ^ k := by
          ring_nf
        have h70 : a * a ^ k + b * b ^ k ≥ (a + b) / 2 * (a ^ k + b ^ k) := by
          have h1110 : a * a ^ k + b * b ^ k - ((a + b) / 2 * (a ^ k + b ^ k)) = (a - b) * (a ^ k - b ^ k) / 2 := by
            field_simp
            ring
          have h11910 : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
            have h1121221 : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
              have hk6 : k ≥ 2 := by linarith
              have hk1 : (a - b) * (a ^ k - b ^ k) ≥ 0 := by
                by_cases h' : a ≥ b
                · -- In this case, a - b ≥ 0
                  have h121121 : a ^ k ≥ b ^ k := by
                    apply pow_le_pow_left
                    all_goals
                      nlinarith
                  have h121122 : a ^ k - b ^ k ≥ 0 := by linarith
                  nlinarith
                · -- In this case, a - b ≤ 0
                  have h122121 : a ^ k ≤ b ^ k := by
                    apply pow_le_pow_left
                    all_goals
                      nlinarith
                  have h122122 : a ^ k - b ^ k ≤ 0 := by linarith
                  nlinarith
              nlinarith
            nlinarith
          have h121 : (a - b) * (a ^ k - b ^ k) / 2 ≥ 0 := by
            apply div_nonneg
            linarith
            norm_num
          linarith
        have h80 : (a * a ^ k + b * b ^ k) ≥ (a + b) / 2 * (a ^ k + b ^ k) := by linarith
        have h90 : a ^ (k + 1) + b ^ (k + 1) ≥ 2 * ((a + b) / 2) ^ (k + 1) := by
          calc
            a ^ (k + 1) + b ^ (k + 1) = a * a ^ k + b * b ^ k := by
              ring_nf
            _ ≥ (a + b) / 2 * (a ^ k + b ^ k) := by
              nlinarith [h50, h70]
            _ ≥ (a + b) / 2 * (2 * ((a + b) / 2) ^ k) := by
              apply mul_le_mul_of_nonneg_left
              linarith
              all_goals
                positivity
              all_goals
                nlinarith
            _ = 2 * ((a + b) / 2) ^ (k + 1) := by
              ring_nf
              <;> field_simp
              <;> ring
        linarith
      exact Nat.le_induction base2 step2 n (by linarith)
    nlinarith
  linarith
import Mathlib

open Real

theorem inequalities_282804 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (n : ℕ) (hn : 0 < n) :
    (a^n + b^n) / 2 ≥ ((a + b) / 2)^n := by
  have h1 : (a ^ n + b ^ n) / 2 ≥ ((a + b) / 2) ^ n := by
    have h2 : ∀ n : ℕ, (a ^ n + b ^ n) / 2 ≥ ((a + b) / 2) ^ n := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have h3 : (a ^ (n + 1) + b ^ (n + 1)) / 2 ≥ ((a + b) / 2) ^ (n + 1 : ℕ) := by
          have h4 : (a ^ (n + 1) + b ^ (n + 1)) / 2 ≥ ((a ^ n + b ^ n) / 2) * ((a + b) / 2) := by
            have h5 : (a ^ (n + 1) + b ^ (n + 1)) ≥ (a ^ n + b ^ n) * ((a + b) / 2) := by
              have h8 : 2 * (a ^ (n + 1) + b ^ (n + 1)) ≥ (a ^ n + b ^ n) * (a + b) := by
                have h9 : 2 * (a ^ (n + 1) + b ^ (n + 1)) - (a ^ n + b ^ n) * (a + b) ≥ 0 := by
                  have h10 : 2 * (a ^ (n + 1) + b ^ (n + 1)) - (a ^ n + b ^ n) * (a + b) = (a - b) * (a ^ n - b ^ n) := by
                    ring_nf
                  rw [h10]
                  have h12 : (a - b) * (a ^ n - b ^ n) ≥ 0 := by
                    by_cases h' : a ≥ b
                    · 
                      have h13 : a - b ≥ 0 := by linarith
                      have h14 : a ^ n ≥ b ^ n := by
                        apply pow_le_pow_left
                        all_goals
                          try linarith
                      have h15 : a ^ n - b ^ n ≥ 0 := by linarith
                      nlinarith
                    · 
                      have h16 : b ≥ a := by linarith
                      have h17 : a - b ≤ 0 := by linarith
                      have h18 : a ^ n ≤ b ^ n := by
                        apply pow_le_pow_left
                        all_goals
                          try linarith
                      have h19 : a ^ n - b ^ n ≤ 0 := by linarith
                      nlinarith
                  linarith
                nlinarith
              have h11 : (a ^ (n + 1) + b ^ (n + 1)) ≥ (a ^ n + b ^ n) * ((a + b) / 2) := by
                linarith
              linarith
            nlinarith
          have h7 : ((a ^ n + b ^ n) / 2) * ((a + b) / 2) ≥ ((a + b) / 2) ^ (n + 1 : ℕ) := by
            have h8 : ((a + b) / 2) ^ (n + 1 : ℕ) = ((a + b) / 2) ^ n * ((a + b) / 2) := by ring
            have h9 : ((a ^ n + b ^ n) / 2) ≥ ((a + b) / 2) ^ n := by
              linarith [ih]
            have h10 : ((a ^ n + b ^ n) / 2) * ((a + b) / 2) ≥ ((a + b) / 2) ^ n * ((a + b) / 2) := by
              apply mul_le_mul_of_nonneg_right
              linarith
              have h11 : 0 ≤ (a + b) / 2 := by
                nlinarith
              all_goals
                nlinarith
            have h11 : ((a + b) / 2) ^ n * ((a + b) / 2) = ((a + b) / 2) ^ (n + 1 : ℕ) := by ring
            nlinarith
          nlinarith
        simp [pow_succ] at *
        all_goals
          linarith
    specialize h2 n
    linarith
  linarith
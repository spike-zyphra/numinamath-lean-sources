import Mathlib

theorem inequalities_179538 (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hn : 0 < n) :
    (a^n + b^n) / 2 ≥ ((a + b) / 2)^n := by
  have h1 : n ≥ 1 := by linarith
  have h2 : ∀ m : ℕ, m ≥ 1 → (a ^ m + b ^ m) / 2 ≥ ((a + b) / 2) ^ m := by
    intro m hm
    have h7 : m ≥ 1 := hm
    have h8 : (a ^ m + b ^ m) / 2 ≥ ((a + b) / 2) ^ m := by
      have base : (a ^ 1 + b ^ 1) / 2 ≥ ((a + b) / 2) ^ 1 := by
        nlinarith
      have step : ∀ k : ℕ, k ≥ 1 → (a ^ k + b ^ k) / 2 ≥ ((a + b) / 2) ^ k → 
        (a ^ (k + 1) + b ^ (k + 1)) / 2 ≥ ((a + b) / 2) ^ (k + 1) := by
        intro k hk h
        have h9 : 0 ≤ a := by linarith
        have h10 : 0 ≤ b := by linarith
        have h11 : (a ^ (k + 1) + b ^ (k + 1)) / 2 ≥ ((a + b) / 2) * ((a ^ k + b ^ k) / 2) := by
          have h19 : (a ^ (k + 1) + b ^ (k + 1) ) / 2 - ((a + b) / 2) * ((a ^ k + b ^ k) / 2) ≥ (0 : ℝ) := by
            have h13 : (a ^ (k + 1) + b ^ (k + 1) ) / 2 - ( (a + b) / 2 ) * ( (a ^ k + b ^ k ) / 2 ) = 
              ( ( a * ( a ^ k ) + b * ( b ^ k ) ) / 2 - ( a * ( a ^ k ) + a * ( b ^ k ) + b * ( a ^ k ) + b * ( b ^ k ) ) / 4 ) := by
                ring_nf
            rw [h13]
            have h14 : ( a * ( a ^ k ) + b * ( b ^ k ) ) / 2 - ( a * ( a ^ k ) + a * ( b ^ k ) + b * ( a ^ k ) + b * ( b ^ k ) ) / 4 ≥ 0 := by
                have h15 : ( a * ( a ^ k ) + b * ( b ^ k ) ) / 2 - ( a * ( a ^ k ) + a * ( b ^ k ) + b * ( a ^ k ) + b * ( b ^ k ) ) / 4 = (a - b) * (a ^ k - b ^ k) / 4 := by 
                  ring_nf 
                rw [h15] 
                have h16 : (a - b) * (a ^ k - b ^ k) ≥ 0 := by 
                  by_cases h17 : a ≥ b 
                  · 
                    have h18 : a - b ≥ 0 := by nlinarith 
                    have h19 : a ^ k ≥ b ^ k := by 
                      apply pow_le_pow_left 
                      all_goals linarith 
                      all_goals nlinarith 
                    have h20 : a ^ k - b ^ k ≥ 0 := by linarith 
                    nlinarith 
                  · 
                    have h18 : a < b := by nlinarith 
                    have h19 : a - b < 0 := by nlinarith 
                    have h20 : a ^ k < b ^ k := by 
                      apply pow_lt_pow_left 
                      all_goals nlinarith 
                      all_goals nlinarith 
                    have h21 : a ^ k - b ^ k < 0 := by linarith 
                    nlinarith 
                linarith 
            linarith 
          linarith 
        have h12 : ((a + b) / 2) ^ (k + 1) = ((a + b) / 2) * ((a + b) / 2) ^ k := by ring 
        have h17 : ((a + b) / 2) * ((a + b) / 2) ^ k ≤ (a ^ (k + 1) + b ^ (k + 1)) / 2 := by 
          nlinarith [h11, pow_nonneg (show 0 ≤ (a : ℝ) by linarith) k, pow_nonneg (show 0 ≤ (b : ℝ) by linarith) k] 
        have h13 : ((a + b) / 2) ^ (k + 1) ≤ (a ^ (k + 1) + b ^ (k + 1)) / 2 := by 
          nlinarith [h12, h17] 
        linarith 
      exact Nat.le_induction base step m h7
    linarith 
  specialize h2 n (by linarith)
  simpa using h2
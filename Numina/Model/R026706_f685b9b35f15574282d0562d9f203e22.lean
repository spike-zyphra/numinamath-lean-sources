import Mathlib


theorem inequalities_308777 (a b : ℝ) (n : ℕ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a^n + b^n) / 2 ≥ ((a + b) / 2)^n := by
  have h : (a ^ n + b ^ n) ≥ 2 * (( (a + b) / 2 ) ^ n) := by
    have h22 : ∀ (n : ℕ), (a ^ n + b ^ n) ≥ 2 * (( (a + b) / 2 ) ^ n ) := by
      intro n
      induction n with
      | zero =>
        norm_num
      | succ n ih =>
        have h3 : a ^ (n + 1) + b ^ (n + 1) ≥ ( (a + b) / 2 ) * ( a ^ n + b ^ n ) := by
          have h2 : 2 * (a ^ (n + 1) + b ^ (n + 1)) ≥ (a + b) * (a ^ n + b ^ n) := by
            have h7 : 2 * (a ^ (n + 1) + b ^ (n + 1)) - ( (a + b) * (a ^ n + b ^ n ) ) ≥ 0 := by
              have h8 : 2 * (a ^ (n + 1) + b ^ (n + 1)) - ( (a + b) * (a ^ n + b ^ n ) ) = (a - b) * (a ^ n - b ^ n : ℝ) := by
                ring_nf
              rw [h8]
              have h9 : (a - b) * (a ^ n - b ^ n : ℝ) ≥ 0 := by
                by_cases h : a ≥ b
                ·
                  have ha10 : a - b ≥ 0 := by linarith
                  have h10 : a ^ n ≥ b ^ n := by
                    apply pow_le_pow_left
                    all_goals
                      nlinarith
                  have ha11 : a ^ n - b ^ n ≥ 0 := by linarith
                  nlinarith
                ·
                  have h11 : b ≥ a := by linarith
                  have ha10 : a - b ≤ 0 := by linarith
                  have h10 : a ^ n ≤ b ^ n := by
                    apply pow_le_pow_left
                    all_goals
                      nlinarith
                  have ha11 : a ^ n - b ^ n ≤ 0 := by linarith
                  nlinarith
              linarith
            linarith
          linarith
        have h9 : (a ^ (n + 1) + b ^ (n + 1) ) ≥ 2 * (( (a + b) / 2 ) ^ (n + 1 : ℕ ) ) := by
          have h8 : (a ^ (n + 1) + b ^ (n + 1) ) ≥ ( (a + b) / 2 ) * ( a ^ n + b ^ n ) := h3
          have h10 : ( (a + b) / 2 ) * ( a ^ n + b ^ n ) ≥ 2 * (( (a + b) / 2 ) ^ (n + 1 : ℕ ) ) := by
            have h11 : ( (a + b) / 2 ) * ( a ^ n + b ^ n ) ≥ (a + b) * (( (a + b) / 2 ) ^ n ) := by
              have h12 : a ^ n + b ^ n ≥ 2 * (( (a + b) / 2 ) ^ n ) := ih
              nlinarith
            have h7 : (a + b) * (( (a + b) / 2 ) ^ n ) = 2 * (( (a + b) / 2 ) ^ (n + 1 : ℕ ) ) := by
              ring_nf
            nlinarith [h7]
          nlinarith
        simpa using h9
    specialize h22 n
    linarith
  linarith
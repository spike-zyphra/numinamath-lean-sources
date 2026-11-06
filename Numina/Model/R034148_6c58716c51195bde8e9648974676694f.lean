import Mathlib

theorem inequalities_598579 (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (n : ℕ) (hn : 0 < n) :
    (a ^ n + b ^ n) / 2 ≥ ((a + b) / 2) ^ n := by 
  have h2 : a ^ n + b ^ n ≥ 2 * ((a + b) / 2) ^ n := by
    have h3 : ∀ k : ℕ, a ^ k + b ^ k ≥ 2 * ((a + b) / 2) ^ k := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h2 : a ^ (k + 1) + b ^ (k + 1) ≥ (a + b) / 2 * (a ^ k + b ^ k) := by
          have h4 : a ^ (k + 1) + b ^ (k + 1) - (a + b) / 2 * (a ^ k + b ^ k) ≥ 0 := by
            have h5 : a ^ (k + 1) + b ^ (k + 1) - (a + b) / 2 * (a ^ k + b ^ k) =
          (a ^ k - b ^ k) * (a - b) / 2 := by ring
            rw [h5]
            by_cases h : a ≥ b
            · -- If a ≥ b, then a - b ≥ 0
              have h1 : a - b ≥ 0 := by linarith
              have h6 : a ^ k ≥ b ^ k := by
                apply pow_le_pow_left
                all_goals linarith
              have h7 : a ^ k - b ^ k ≥ 0 := by linarith
              have h8 : (a ^ k - b ^ k) * (a - b) ≥ 0 := mul_nonneg h7 h1
              linarith
            · -- If b > a, then a - b ≤ 0
              have h1 : a - b ≤ 0 := by linarith
              have h6 : a ^ k ≤ b ^ k := by
                apply pow_le_pow_left
                all_goals linarith
              have h7 : a ^ k - b ^ k ≤ 0 := by linarith
              have h8 : (a ^ k - b ^ k) * (a - b) ≥ 0 := mul_nonneg_of_nonpos_of_nonpos h7 h1
              linarith
          linarith only [h4]
          all_goals linarith
        have h4 : ((a + b) / 2) ^ (k + 1) = ((a + b) / 2) * ((a + b) / 2) ^ k := by ring
        nlinarith [ih]
    exact h3 n
  linarith
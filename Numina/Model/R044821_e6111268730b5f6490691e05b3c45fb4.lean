import Mathlib

theorem number_theory_200720 :
    ∀ n : ℕ, ∃ a b c : ℕ,
      a^15 + b^15 = c^16 ∧
      a > n ∧ b > n ∧ c > n := by
  intro n
  use 2 ^ (1 + 16 * (n + 1)), 2 ^ (1 + 16 * (n + 1)), 2 ^ (1 + 15 * (n + 1))
  constructor
  · -- Verify the equation
    ring_nf
  constructor
  · -- Show a > n
    have h2 : ∀ (k : ℕ), 2 ^ (1 + 16 * ((k : ℕ) + 1)) > (k : ℕ) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h3 : 2 ^ (1 + 16 * ((k + 1 + 1) : ℕ)) = 2 ^ (1 + 16 * ((k + 1) : ℕ)) * 2 ^ 16 := by
          ring_nf
        rw [h3]
        have h4_pos : (2 : ℕ) ^ 16 > 0 := by
          norm_num
        have h5_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1) : ℕ)) > (k : ℕ) := by
          linarith [ih]
        have h6_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1 : ℕ))) * (2 : ℕ) ^ 16 > (k + 1 : ℕ) := by
          have h7_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1 : ℕ))) > (k : ℕ) := by
            linarith [ih]
          nlinarith [h7_pos, h4_pos, pow_pos (show (0 : ℕ) < 2 by norm_num) 16, pow_pos (show (0 : ℕ) < 2 by norm_num) 2]
        linarith [h6_pos]
    have h3_pos := h2 n
    have h3_pos' : (2 : ℕ) ^ (1 + 16 * ((n + 1 : ℕ))) > (n : ℕ) := by
      simpa using h3_pos
    linarith
  constructor
  · -- Show b > n
    have h2 : ∀ (k : ℕ), 2 ^ (1 + 16 * ((k : ℕ) + 1)) > (k : ℕ) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h3 : 2 ^ (1 + 16 * ((k + 1 + 1) : ℕ)) = 2 ^ (1 + 16 * ((k + 1) : ℕ)) * 2 ^ 16 := by
          ring_nf
        rw [h3]
        have h4_pos : (2 : ℕ) ^ 16 > 0 := by
          norm_num
        have h5_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1) : ℕ)) > (k : ℕ) := by
          linarith [ih]
        have h6_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1 : ℕ))) * (2 : ℕ) ^ 16 > (k + 1 : ℕ) := by
          have h7_pos : (2 : ℕ) ^ (1 + 16 * ((k + 1 : ℕ))) > (k : ℕ) := by
            linarith [ih]
          nlinarith [h7_pos, h4_pos, pow_pos (show (0 : ℕ) < 2 by norm_num) 16, pow_pos (show (0 : ℕ) < 2 by norm_num) 2]
        linarith [h6_pos]
    have h3_pos := h2 n
    have h3_pos' : (2 : ℕ) ^ (1 + 16 * ((n + 1 : ℕ))) > (n : ℕ) := by
      simpa using h3_pos
    linarith
  · -- Show c > n
    have h2 : ∀ (k : ℕ), 2 ^ (1 + 15 * ((k : ℕ) + 1)) > (k : ℕ) := by
      intro k
      induction k with
      | zero =>
        norm_num
      | succ k ih =>
        have h3 : 2 ^ (1 + 15 * ((k + 1 + 1) : ℕ)) = (2 ^ (1 + 15 * ((k + 1) : ℕ))) * 2 ^ 15 := by
          ring_nf
        rw [h3]
        have h4_pos : (2 : ℕ) ^ 15 > 0 := by
          norm_num
        have h5_pos : (2 : ℕ) ^ (1 + 15 * ((k + 1) : ℕ)) > (k : ℕ) := by
          linarith [ih]
        have h6_pos : (2 : ℕ) ^ (1 + 15 * ((k + 1 : ℕ))) * (2 : ℕ) ^ 15 > (k + 1 : ℕ) := by
          have h7_pos : (2 : ℕ) ^ (1 + 15 * ((k + 1 : ℕ))) > (k : ℕ) := by
            linarith [ih]
          nlinarith [h7_pos, h4_pos, pow_pos (show (0 : ℕ) < 2 by norm_num) 15, pow_pos (show (0 : ℕ) < 2 by norm_num) 2]
        linarith [h6_pos]
    have h3_pos := h2 n
    have h3_pos' : (2 : ℕ) ^ (1 + 15 * ((n + 1 : ℕ))) > (n : ℕ) := by
      simpa using h3_pos
    linarith
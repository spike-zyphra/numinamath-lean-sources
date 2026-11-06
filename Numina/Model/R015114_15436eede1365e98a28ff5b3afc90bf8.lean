import Mathlib

theorem algebra_186795 (x : ℕ) : 9 ^ x + 4 * 3 ^ (x + 1) = 13 ↔ x = 0 := by
  constructor
  · -- Forward direction: if the equation holds, then x = 0.
    intro h
    have h1 : x = 0 := by
      have eq1 : 9 ^ x + 4 * 3 ^ (x + 1) = 13 := h
      have eq2 : 9 ^ x = 3 ^ (2 * x : ℕ) := by
        rw [show 9 = 3 ^ 2 by norm_num]
        rw [← pow_mul]
      have eq3 : 4 * 3 ^ (x + 1 : ℕ) = 12 * 3 ^ x := by
        ring_nf
      rw [eq2] at eq1
      rw [eq3] at eq1
      have h2 : 3 ^ (2 * x : ℕ) = (3 ^ x) ^ 2 := by
        ring_nf
      rw [h2] at eq1
      have h3 : (3 ^ x : ℕ) ^ 2 + 12 * (3 ^ x : ℕ) = 13 := by
        omega
      have h4 : (3 ^ x : ℕ) ≤ 1 := by
        nlinarith [show (3 ^ x : ℕ) ≥ 1 from by
          have h7 : (3 ^ x : ℕ) ≥ 1 := by
            have h8 : (3 : ℕ) ^ x ≥ (1 : ℕ) := by
              apply Nat.one_le_pow
              all_goals linarith
            linarith
          linarith
        ]
      have h6 : (3 ^ x : ℕ) ≥ 1 := by
        have h7 : (3 ^ x : ℕ) ≥ 1 := by
          have h8 : (3 : ℕ) ^ x ≥ (1 : ℕ) := by
            apply Nat.one_le_pow
            all_goals linarith
          linarith
        linarith
      have h5 : (3 ^ x : ℕ) = 1 := by
        nlinarith
      have h6 : x = 0 := by
        have h7 : (3 : ℕ) ^ x = 1 := h5
        have h8 : x = 0 := by
          have h9 : (3 : ℕ) ^ x = 1 := h7
          have h10 : x = 0 := by
            have h11 : (3 : ℕ) ^ x = 1 := h9
            exact Nat.pow_right_injective (by norm_num) h11
          linarith
        linarith
      exact h6
    exact h1
  · -- Backward direction: if x = 0, then the equation holds.
    intro h
    rw [h]
    all_goals norm_num
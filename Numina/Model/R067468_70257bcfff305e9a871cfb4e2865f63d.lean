import Mathlib

theorem algebra_188034 (x : ℕ) (hx : x > 0) : (2 ^ x + 10) / 4 = 9 / 2 ^ (x - 2) ↔ x = 3 := by
  constructor
  · -- Assume the equation holds, prove $x = 3$.
    intro h
    have h1 : x ≤ 5 := by
      by_contra h2
      push_neg at h2
      have h2' : x ≥ 6 := by omega
      have h3 : (2 ^ x + 10) / 4 = 9 / 2 ^ (x - 2) := h
      have h4 : (2 ^ x + 10) / 4 > 0 := by
        have h5 : 2 ^ x ≥ 2 := by
          have h6 : x ≥ 1 := by linarith
          have h7 : ∀ k : ℕ, (k ≥ 1) → 2 ^ k ≥ 2 := by
            intro k hk
            induction k with
            | zero => linarith
            | succ k ih =>
              cases k with
              | zero =>
                omega
              | succ k =>
                omega
          specialize h7 x (show x ≥ 1 by linarith)
          linarith
        omega
      have h5 : 9 / 2 ^ (x - 2) = 0 := by
        have h6 : x - 2 ≥ 4 := by
          omega
        have h7 : 2 ^ (x - 2) > 9 := by
          have h8 : 2 ^ (x - 2) ≥ 16 := by
            have h9 : x - 2 ≥ 4 := h6
            have h10 : 2 ^ (x - 2) ≥ 2 ^ 4 := by
              apply Nat.pow_le_pow_of_le_right (by norm_num) h9
            norm_num at h10 ⊢
            linarith
          omega
        rw [Nat.div_eq_zero_iff]
        omega
      omega
    have h6 : x ≤ 5 := by omega
    interval_cases x <;> norm_num at h ⊢ <;> all_goals omega
  · -- Assume $x = 3$, prove the equation.
    intro h
    rw [h]
    all_goals norm_num
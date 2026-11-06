import Mathlib

theorem algebra_18610 (x : ℕ) : 2^8=4^x ↔ x=4 := by 
  constructor
  · -- Assume $2^8 = 4^x$, prove $x = 4$
    intro h
    have h1 : 4 ^ x = 2 ^ 8 := by
      linarith
    have h2 : 4 ^ x = 2 ^ (2 * x) := by
      rw [show 4 = 2 ^ 2 by rfl]
      rw [← pow_mul]
      all_goals linarith
    rw [h2] at h1
    have h3 : 2 * x = 8 := by
      exact Nat.pow_right_injective (by norm_num) h1
    have : x = 4 := by
      linarith
    exact this
  · -- Assume $x = 4$, prove $2^8 = 4^x$
    intro h
    rw [h]
    all_goals norm_num
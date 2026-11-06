import Mathlib

theorem algebra_265684 (x : ℕ) : ((10^3 * 10^x)^2 = 10^18) ↔ x = 6 := by
  constructor
  · -- Assume ((10 ^ 3 * 10 ^ x) ^ 2 = 10 ^ 18) prove x = 6
    intro h
    have h1 : 10 ^ 3 * 10 ^ x = 10 ^ (3 + x) := by
      ring_nf
    have h4 : (10 ^ 3 * 10 ^ x) ^ 2 = (10 ^ (3 + x)) ^ 2 := by
      rw [h1]
    have h5 : (10 ^ (3 + x)) ^ 2 = 10 ^ (6 + 2 * x) := by
      rw [← pow_mul]
      ring_nf
      all_goals omega
    have h3 : (10 ^ (3 + x)) ^ 2 = 10 ^ 18 := by
      have h6 : (10 ^ 3 * 10 ^ x) ^ 2 = (10 ^ (3 + x)) ^ 2 := h4
      have h7 : (10 ^ 3 * 10 ^ x) ^ 2 = 10 ^ 18 := h
      linarith
    -- Now the equation 10^(6+2x) = 10^18, so exponents must be equal.
    have h6 : (10 ^ (6 + 2 * x)) = 10 ^ 18 := by
      have h7 : (10 ^ (3 + x)) ^ 2 = 10 ^ (6 + 2 * x) := h5
      linarith [h3, h7]
    have h7 : (6 + 2 * x) = 18 := by
      have h8 : (10 : ℕ) ^ (6 + 2 * x) = (10 : ℕ) ^ (18) := h6
      exact Nat.pow_right_injective (by norm_num) h8
    omega
  · -- Assume x = 6 prove ((10 ^ 3 * 10 ^ x) ^ 2 = 10 ^ 18)
    intro h
    rw [h]
    norm_num
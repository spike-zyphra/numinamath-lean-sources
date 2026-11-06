import Mathlib

theorem algebra_273863 (x : ℕ) : 10^x * 10^5 = 100^4 ↔ x = 3 := by
  constructor
  · -- Assume 10^x * 10^5 = 100^4, prove x = 3
    intro h
    have h1 : x ≤ 10 := by
      by_contra hx
      push_neg at hx
      have h5 : x ≥ 11 := by omega
      have eq1 : 10^x * 10^5 ≥ 10^11 * 10^5 := by
        have h5a : 10^x ≥ 10^11 := by
          have h5a : x ≥ 11 := h5
          have : 10^x ≥ 10^11 := by
            apply Nat.pow_le_pow_of_le_right (by norm_num) h5a
          linarith
        nlinarith
      norm_num at eq1
      norm_num [show 100^4 = 10^8 by norm_num] at h
      omega
    have h2 : 10^x * 10^5 = 100^4 := h
    have h3 : 10^x * 10^5 = 10 ^ (x + 5) := by
      ring_nf
    have h4 : (10 ^ (x + 5) : ℕ) = (100 ^ 4 : ℕ) := by
      linarith [h2, h3]
    have h5 : (100 : ℕ) ^ 4 = 10 ^ 8 := by
      norm_num
    rw [h5] at h4
    have h6 : x + 5 = 8 := by
      exact Nat.pow_right_injective (by norm_num) h4
    omega
  · -- Assume x = 3, prove 10^x * 10^5 = 100^4
    intro h
    rw [h]
    all_goals norm_num
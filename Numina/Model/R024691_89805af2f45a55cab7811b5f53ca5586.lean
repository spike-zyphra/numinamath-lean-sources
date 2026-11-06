import Mathlib

theorem algebra_145324 (x : ℕ) :
    2 * 3^(x - 3) + 3^(x - 2) + 3^(x - 1) = 14 * 3^5 ↔ x = 8 := by
  constructor
  · -- Assume left side, prove right side
    intro h
    have h1 : x ≥ 3 := by
      by_contra h2
      push_neg at h2
      interval_cases x <;> norm_num at h <;> omega

    have eq1 : 2 * 3^(x - 3) + 3^(x - 2) + 3^(x - 1) = 14 * 3^(x - 3) := by
      have h2 : x ≥ 3 := h1
      have h3 : x - 2 = (x - 3) + 1 := by omega
      have h4 : x - 1 = (x - 3) + 2 := by omega
      rw [h3, h4]
      have h5 : 3^((x - 3) + 1) = 3^(x - 3) * 3 := by ring
      have h6 : 3^((x - 3) + 2) = 3^(x - 3) * 9 := by
        ring_nf
      rw [h5, h6]
      ring_nf
    have eq2 : 14 * 3^(x - 3) = 14 * 3^5 := by
      linarith [h, eq1]
    have h3 : x - 3 = 5 := by
      have h4 : 14 * 3^(x - 3) = 14 * 3^5 := eq2
      have h5 : 3^(x - 3) = 3^5 := by
        nlinarith
      have h6 : x - 3 = 5 := by
        exact Nat.pow_right_injective (by norm_num) h5
      exact h6
    omega
  · -- Assume right side, prove left side
    intro h
    rw [h]
    norm_num
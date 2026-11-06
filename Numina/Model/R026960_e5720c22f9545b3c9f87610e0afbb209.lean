import Mathlib

theorem algebra_275391 (x : ℕ) : (2^4 * 3^6 = 9 * 6^x) ↔ x = 4 := by
  constructor
  · -- Assume 2^4 * 3^6 = 9 * 6^x, prove x = 4
    intro h
    have h1 : 2^4 * 3^6 = 9 * 6^x := h
    have eq1 : 9 * 6^x = 11664 := by
      norm_num at h1 ⊢
      omega
    have eq2 : 6^x = 1296 := by
      omega
    have eq3 : x = 4 := by
      have h3 : 6^x = 1296 := eq2
      have h4 : x ≤ 4 := by
        by_contra h5
        push_neg at h5
        have h5' : x ≥ 5 := by omega
        have h6 : 6 ^ x ≥ 6 ^ 5 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals omega
        have h7 : 6 ^ 5 = 7776 := by norm_num
        have h8 : 6 ^ x ≥ 7776 := by
          linarith [h6, h7]
        linarith [h3, h8]
      interval_cases x <;> norm_num at h3 ⊢ <;> omega
    exact_mod_cast eq3
  · -- Assume x = 4, prove 2^4 * 3^6 = 9 * 6^x
    intro h
    rw [h]
    all_goals norm_num
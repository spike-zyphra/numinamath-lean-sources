import Mathlib

theorem algebra_292618 (x : ℕ) (hx : 5^(2*x) - 6 * 5^x + 5 = 0) :
    x = 1 ∨ x = 0 := by 
  have h1 : 5 ^ (2 * x) = (5 ^ x) ^ 2 := by 
    ring_nf
  rw [h1] at hx
  have h2 : (5 ^ x : ℕ) ≤ 6 := by
    by_contra h
    push_neg at h
    have h3 : (5 ^ x : ℕ) ≥ 7 := by
      omega
    have h4 : (5 ^ x) ^ 2 ≥ 7 * (5 ^ x) := by
      nlinarith [h3]
    have h5 : (5 ^ x : ℕ) ^ 2 - 6 * (5 ^ x) + 5 > 0 := by
      have h6 : (5 ^ x : ℕ) ^ 2 ≥ 7 * (5 ^ x) := h4
      omega
    omega
  have h3 : x ≤ 1 := by
    by_contra h
    push_neg at h
    have h4 : x ≥ 2 := by
      omega
    have h5 : (5 ^ x : ℕ) ≥ 25 := by
      have h6 : (5 : ℕ) ^ x ≥ (5 : ℕ) ^ 2 := by
        have h7 : x ≥ 2 := h4
        have h8 : (5 : ℕ) ^ x ≥ (5 : ℕ) ^ 2 := by
          apply Nat.pow_le_pow_of_le_right
          all_goals
            omega
        linarith
      have h9 : (5 : ℕ) ^ 2 = 25 := by
        norm_num
      linarith [h6, h9]
    have h6 : (5 ^ x : ℕ) > 6 := by
      omega
    omega
  have h4 : x = 0 ∨ x = 1 := by 
    interval_cases x <;> tauto
  tauto
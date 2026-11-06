import Mathlib

theorem algebra_3714 (n : ℕ) (h : n > 0) (h1 : n * (n + 1) * (n + 2) * (n + 3) = 840) :
    n + 3 = 7 := by
  have h2 : n ≤ 7 := by
    by_contra h2
    push_neg at h2
    have h3 : n ≥ 8 := by omega
    have h4 : n * (n + 1) * (n + 2) * (n + 3) ≥ 8 * 9 * 10 * 11 := by
      have h8 : n ≥ 8 := h3
      have h9 : n + 1 ≥ 9 := by omega
      have h10 : n + 2 ≥ 10 := by omega
      have h11 : n + 3 ≥ 11 := by omega
      have h12 : n * (n + 1) * (n + 2) * (n + 3) ≥ 8 * 9 * 10 * 11 := by
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        apply Nat.mul_le_mul
        all_goals linarith
      linarith
    have h5 : n * (n + 1) * (n + 2) * (n + 3) ≥ 7920 := by
      norm_num at h4 ⊢
      linarith
    linarith
  interval_cases n <;> omega
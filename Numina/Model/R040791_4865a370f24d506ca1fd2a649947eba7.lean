import Mathlib

theorem number_theory_7489 {n : ℕ} (hn : 0 < n) (h : 2^n - 1 = (3 * n + 1) * (3 * n + 3)) :
    n = 10 := by
  have h1 : n ≥ 1 := by linarith
  have h2 : n ≤ 10 := by
    by_contra h2
    push_neg at h2
    have h3 : n ≥ 11 := by linarith
    have h4 : ∀ (k : ℕ), k ≥ 11 → 2 ^ k > 9 * k ^ 2 + 12 * k + 4 := by
      intro k hk
      have base11 : 2 ^ 11 > 9 * 11 ^ 2 + 12 * 11 + 4 := by norm_num
      have step : ∀ (m : ℕ), m ≥ 11 → 2 ^ m > 9 * m ^ 2 + 12 * m + 4 → 2 ^ (m + 1) > 9 * (m + 1) ^ 2 + 12 * (m + 1) + 4 := by
        intro m hm h
        have h6 : 2 ^ (m + 1) = 2 * (2 ^ m) := by ring
        have h5 : 2 ^ (m + 1) > 2 * (9 * m ^ 2 + 12 * m + 4) := by
          rw [h6]
          linarith [h]
        have h7 : 2 * (9 * m ^ 2 + 12 * m + 4) > 9 * (m + 1) ^ 2 + 12 * (m + 1) + 4 := by
          nlinarith [sq_nonneg (m - 11 : ℤ), sq_nonneg (m : ℤ)]
        linarith [h5, h7]
      exact Nat.le_induction base11 step k hk
    have h5 : 2 ^ n > 9 * n ^ 2 + 12 * n + 4 := h4 n h3
    have h7 : (3 * n + 1) * (3 * n + 3) = 9 * n ^ 2 + 12 * n + 3 := by
      ring_nf
      <;> omega
    have h6 : 2 ^ n - 1 > (3 * n + 1) * (3 * n + 3) := by
      have h8 : 2 ^ n > 9 * n ^ 2 + 12 * n + 4 := h5
      omega
    nlinarith [h, h6]
  interval_cases n <;> norm_num at h ⊢ <;> omega
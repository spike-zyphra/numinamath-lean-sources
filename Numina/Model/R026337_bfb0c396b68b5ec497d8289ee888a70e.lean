import Mathlib

theorem algebra_155772 (n : ℕ) (h : n > 0) (h1 : ∃ k, n^3 + 2 * n^2 + 9 * n + 8 = k^3) :
    n = 7 := by
  rcases h1 with ⟨k, hk⟩
  have h2 : k > n := by
    by_contra h3
    push_neg at h3
    have h4 : k ≤ n := by omega
    have h5 : k^3 ≤ n^3 := by
      have h6 : k ≤ n := h4
      have h7 : k^3 ≤ n^3 := by
        apply Nat.pow_le_pow_left
        all_goals omega
      linarith
    have h8 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 ≤ n^3 := by
      linarith [hk, h5]
    nlinarith [sq_pos_of_pos (show 0 < (n : ℕ) by linarith)]
  have h3 : k < n + 2 := by
    by_contra h4
    push_neg at h4
    have h5 : k ≥ n + 2 := by omega
    have h6 : k^3 ≥ (n + 2) ^ 3 := by
      have h7 : k ≥ n + 2 := h5
      have h8 : k^3 ≥ (n + 2) ^ 3 := by
        apply Nat.pow_le_pow_left
        all_goals omega
      linarith
    have h7 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 ≥ (n + 2) ^ 3 := by
      linarith [hk, h6]
    nlinarith [sq_pos_of_pos (show 0 < (n : ℕ) by linarith), sq_nonneg ((n + 1 : ℕ))]
  have h8 : k = n + 1 := by
    linarith
  rw [h8] at hk
  have h9 : n ^ 3 + 2 * n ^ 2 + 9 * n + 8 = (n + 1) ^ 3 := by
    linarith [hk]
  have h10 : n = 7 := by
    have h12 : (n : ℕ) ≤ 14 := by
      nlinarith [sq_nonneg ((n : ℕ) - 7 : ℤ), h9]
    interval_cases n <;> omega
  exact h10
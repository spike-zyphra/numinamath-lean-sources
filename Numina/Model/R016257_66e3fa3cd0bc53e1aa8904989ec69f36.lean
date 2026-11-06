import Mathlib

theorem algebra_117938 {n : ℕ} (hn : n > 0) (h : ∃ k, k^2 = n^4 + 2*n^3 + 6*n^2 + 12*n + 25) :
    n = 8 := by
  rcases h with ⟨k, hk⟩
  have h1 : k^2 = n^4 + 2*n^3 + 6*n^2 + 12*n + 25 := by
    exact_mod_cast hk
  have h2 : k > n^2 + n := by
    by_contra h
    push_neg at h
    have h3 : k ≤ n^2 + n := by linarith
    have h4 : k^2 ≤ (n^2 + n) ^ 2 := by
      nlinarith [h3]
    have h5 : n^4 + 2 * n^3 + 6 * n^2 + 12 * n + 25 > (n^2 + n) ^ 2 := by
      nlinarith [sq_pos_of_pos (show 0 < n by linarith), sq_pos_of_pos (show 0 < (n + 1 : ℕ) by linarith)]
    nlinarith [h1, h4, h5]
  have h3 : k < n^2 + n + 5 := by
    by_contra h
    push_neg at h
    have h4 : k ≥ n^2 + n + 5 := by linarith
    have h5 : k^2 ≥ (n^2 + n + 5) ^ 2 := by
      nlinarith [h4]
    have h6 : n^4 + 2 * n^3 + 6 * n^2 + 12 * n + 25 < (n^2 + n + 5) ^ 2 := by
      nlinarith [sq_pos_of_pos (show 0 < n by linarith), sq_pos_of_pos (show 0 < (n + 1 : ℕ) by linarith)]
    nlinarith [h1, h5, h6]
  have h4 : k = n^2 + n + 1 ∨ k = n^2 + n + 2 ∨ k = n^2 + n + 3 ∨ k = n^2 + n + 4 := by
    have h5 : k > n^2 + n := h2
    have h6 : k < n^2 + n + 5 := h3
    have h7 : k ≤ n^2 + n + 4 := by linarith
    have h8 : k ≥ n^2 + n + 1 := by linarith
    omega
  rcases h4 with (h4 | h4 | h4 | h4)
  · -- Assume k = n^2 + n + 1
    rw [h4] at h1
    ring_nf at h1
    have h5 : n ≤ 10 := by
      nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n + 1)]
    interval_cases n <;> omega
  · -- Assume k = n^2 + n + 2
    rw [h4] at h1
    ring_nf at h1
    have h5 : n ≤ 10 := by
      nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n + 1)]
    interval_cases n <;> omega
  · -- Assume k = n^2 + n + 3
    rw [h4] at h1
    ring_nf at h1
    have h5 : n = 8 := by
      nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n + 1)]
    exact_mod_cast h5
  · -- Assume k = n^2 + n + 4
    rw [h4] at h1
    ring_nf at h1
    have h5 : n ≤ 10 := by
      nlinarith [sq_nonneg (n ^ 2), sq_nonneg (n + 1)]
    interval_cases n <;> omega
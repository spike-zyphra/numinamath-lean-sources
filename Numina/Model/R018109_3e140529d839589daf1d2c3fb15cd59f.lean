import Mathlib

theorem number_theory_295120 {n : ℕ} (hn : n > 0) (h : ∃ k, n = k^2 + 5 ∧ ∃ m, n = (m + 7) * m) :
    n ≤ 294 := by
  rcases h with ⟨k, hn1, ⟨m, hn2⟩⟩
  have h_eq : k^2 + 5 = (m + 7) * m := by
    nlinarith
  have h1 : k ≤ m + 3 := by
    by_contra h
    push_neg at h
    have h2 : k ≥ m + 4 := by omega
    have h3 : k^2 ≥ (m + 4) ^ 2 := by
      nlinarith [show k ≥ m + 4 by omega]
    nlinarith [sq_nonneg ((m : ℕ) + 2)]
  have h4 : k = m ∨ k = m + 1 ∨ k = m + 2 ∨ k = m + 3 := by
    have : k ≤ m + 3 := h1
    have : k ≥ m := by 
      by_contra h
      push_neg at h
      have h2 : k < m := by omega
      have h3 : k ≤ m - 1 := by omega
      nlinarith [sq_nonneg ((k : ℕ) - (m : ℕ) : ℤ), sq_nonneg ((m : ℕ) : ℤ)]
    omega
  rcases h4 with (h4 | h4 | h4 | h4)
  · -- Case k = m
    rw [show k = m by linarith [h4]] at h_eq
    have h5 : 7 * m = 5 := by
      nlinarith
    omega
  · -- Case k = m + 1
    rw [show k = m + 1 by linarith [h4]] at h_eq
    have h5 : 5 * m = 6 := by
      nlinarith
    omega
  · -- Case k = m + 2
    rw [show k = m + 2 by linarith [h4]] at h_eq
    have h5 : m = 3 := by
      nlinarith
    have h6 : n = 30 := by
      nlinarith [hn2, h5, hn1, h_eq, h4]
    linarith
  · -- Case k = m + 3
    rw [show k = m + 3 by linarith [h4]] at h_eq
    have h5 : m = 14 := by
      nlinarith
    have h6 : n = 294 := by
      nlinarith [hn2, h5, hn1, h_eq, h4]
    linarith
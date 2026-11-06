import Mathlib

theorem algebra_272046 (n : ℕ) (hn : n > 0) :
    ¬ ∃ k, k^2 = n^4 + 2 * n^3 + 2 * n^2 + 2 * n + 1 := by 
  rintro ⟨k, hk⟩
  have h1 : k ^ 2 = n ^ 4 + 2 * n ^ 3 + 2 * n ^ 2 + 2 * n + 1 := by 
    linarith 
  have h2 : k > n ^ 2 + n := by
    by_contra h 
    push_neg at h
    have h3 : k ^ 2 ≤ (n ^ 2 + n) ^ 2 := by
      nlinarith [sq_nonneg (k - (n^2 + n) : ℤ), h]
    nlinarith [sq_nonneg (n + 1 : ℤ)]
  have h3 : k < n ^ 2 + n + 1 := by 
    by_contra h 
    push_neg at h
    have h4 : k ^ 2 ≥ (n ^ 2 + n + 1) ^ 2 := by 
      nlinarith [sq_nonneg (k - (n ^ 2 + n + 1) : ℤ), h]
    nlinarith [sq_nonneg (n + 1 : ℤ)]
  have h4 : k < n ^ 2 + n + 1 := h3
  have h5 : k > n ^ 2 + n := h2
  have h6 : k ≤ n ^ 2 + n := by
    omega 
  linarith
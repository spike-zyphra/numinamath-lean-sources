import Mathlib

theorem algebra_301137 {A n : ℕ} (hA : ∃ k, k^2 = A) (hA' : A = n^2 + 15 * n + 26) :
    n = 23 := by
  rcases hA with ⟨k, hk⟩
  rw [hA'] at hk
  have h1 : k ^ 2 = n ^ 2 + 15 * n + 26 := by
    linarith
  have h2 : k > n := by
    by_contra h
    push_neg at h
    have h3 : k ≤ n := by
      omega
    have h4 : k ^ 2 ≤ n ^ 2 := by
      nlinarith [h3]
    nlinarith [h1, h4]
  have h3 : k < n + 8 := by
    nlinarith [sq_nonneg (k - (n + 8) : ℤ), sq_nonneg (k - n : ℤ), h1, sq_nonneg ((k : ℤ) - (n : ℤ)), sq_nonneg ((k : ℤ) + (n + 8) : ℤ)]
  have h4 : k ≤ n + 7 := by
    omega
  have h5 : k ≤ n + 7 := h4
  have h6 : k ≥ n + 1 := by
    omega
  by_cases h7 : n ≤ 49
  · -- If n ≤ 49, we can compute manually.
    interval_cases n <;> try { 
      { 
        have : k ≤ 56 := by
          nlinarith 
        interval_cases k <;> omega 
      }
    }
  · -- Assume n > 49
    have h7 : n > 49 := by 
      omega
    exfalso
    nlinarith [sq_nonneg (k - (n + 7) : ℤ), sq_nonneg (k - n : ℤ), sq_nonneg ((k : ℤ) - (n : ℤ)), sq_nonneg ((k : ℤ) + (n : ℤ)), h1]
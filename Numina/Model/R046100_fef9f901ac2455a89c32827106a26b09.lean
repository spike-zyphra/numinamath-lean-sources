import Mathlib

theorem number_theory_293568 (k m n : ℤ) (hk : k > 0) (hm : m > 0) (hn : n > 0)
    (h : m^2 + n = k^2 + k) : m ≤ n := by
  have h1 : m ≤ k := by
    by_contra h4
    push_neg at h4
    have h5 : m > k := h4
    have h2 : m ≥ k + 1 := by
      omega
    have eq1 : n = k ^ 2 + k - m ^ 2 := by 
      linarith
    -- Show that n is non-positive, which contradicts hn : n > 0.
    have h3 : n ≤ 0 := by
      rw [eq1]
      nlinarith [sq_nonneg (m - (k + 1)), sq_nonneg (m), sq_nonneg (k), sq_pos_of_pos hk, h2, sq_pos_of_pos hm]
    -- Contradicts hn : n > 0
    nlinarith
  have h3 : n ≥ k := by
    nlinarith [sq_nonneg (m - k), sq_nonneg (m^2 - k^2), h, sq_nonneg (m - k), sq_nonneg ((k : ℤ) - (m : ℤ)), mul_pos (show 0 < k by omega) (show 0 < m by omega)]
  -- Now, the final part.
  -- Show m <= n.
  have h4 : m ≤ n := by
    nlinarith [sq_nonneg (n - k), mul_pos (show 0 < k by omega) (show 0 < m by omega), sq_nonneg (m - k), h, h1, h3]
  exact h4
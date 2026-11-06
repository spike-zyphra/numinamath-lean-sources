import Mathlib

theorem inequalities_123365 (n : ℕ) (h : n > 4) : 2^n > n^2 := by
  have h1 : n ≥ 5 := by omega
  have base := show 2^5 > 5^2 by norm_num
  have step : ∀ k, k ≥ 5 → 2^k > k^2 → 2^(k + 1) > (k + 1) ^ 2 := by
    intros k hk h_k
    have h1 : 2^(k + 1) = 2 * 2^k := by ring
    rw [h1]
    have h2 : 2 * 2^k > 2 * k^2 := by
      linarith [h_k]
    have h3 : 2 * k^2 > (k + 1) ^ 2 := by
      nlinarith [hk]
    linarith
  exact Nat.le_induction base step n h1
import Mathlib

theorem algebra_6183 {n k : ℝ} (hn : n > 0) (hk : k > 0) (hroots : k^2 + (n - 85) * k - 221 = 0 ∧ (k - 2)^2 / 3 = (2 * n - 12) / 2) : n + k = 98 := by
  obtain ⟨h1, h2⟩ := hroots
  have h3 : (k - 2) ^ 2 * 2 = (2 * n - 12) * 3 := by
    nlinarith
  have eqn2 : n = (k^2 - 4 * k + 22) / 3 := by
    nlinarith [h3]
  rw [eqn2] at h1
  nlinarith [sq_nonneg (k - 17), sq_nonneg (k + 13), sq_nonneg (n - 81), sq_nonneg (n - 34)]
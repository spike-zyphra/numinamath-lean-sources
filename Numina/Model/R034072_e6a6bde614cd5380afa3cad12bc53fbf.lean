import Mathlib

theorem algebra_212920 {a c : ℕ → ℝ} (ha : ∀ n, a n ≠ 0)
    (hroots : ∀ n, a n + a (n - 1) = c n ∧ a n * a (n - 1) = (1 / 3) ^ n)
    (ha1 : a 1 = 2) :
    ∑ i in Finset.range (2 * n), c i = 9 / 2 * (1 - (1 / 3) ^ n) := by
  have h1 := hroots 0
  have h2 := hroots 1
  have h3 : a 0 ^ 2 = 1 := by
    have h0 := hroots 0
    simp [show (0 : ℕ) - 1 = 0 by omega] at h0
    nlinarith
  have h4 : a 0 = 1 / 6 := by
    have h10 := hroots 1
    simp [show (1 : ℕ) - 1 = 0 by omega, ha1] at h10
    linarith
  have h5 : (1 / 6 : ℝ) ^ 2 = 1 := by
    rw [show a 0 = (1 / 6 : ℝ) by linarith] at h3
    linarith
  norm_num at h5
  all_goals exfalso
  all_goals try { tauto }
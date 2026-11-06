import Mathlib

theorem algebra_6775 (k : ℝ) (hk : k ^ 3 = 636056) : k = 86 := by
  have h1 : k ^ 3 - 636056 = 0 := by linarith
  have h2 : (k - 86) * (k ^ 2 + 86 * k + 86 ^ 2) = 0 := by
    ring_nf
    nlinarith [h1]
  cases' (mul_eq_zero.mp h2) with h3 h4
  · -- Case k - 86 = 0, so k = 86
    linarith
  · -- Case k^2 + 86k + 86^2 = 0, show that no real k can satisfy this
    have h5 : k ^ 2 + 86 * k + 86 ^ 2 = 0 := by linarith
    nlinarith [sq_nonneg (k + 43)]
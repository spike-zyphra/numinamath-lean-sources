import Mathlib

theorem algebra_273332 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n, a (n + 2) = 7 * a (n - 1) - 12 * a n) :
    ∀ n, a n = 2 * 3 ^ (n - 1) - 4 ^ (n - 1) := by
  have h0 := han 0
  norm_num at h0
  rw [ha2] at h0
  omega
import Mathlib

theorem algebra_3500 {S : ℕ → ℤ} (h : ∀ n, S (n + 1) = S n + (-1)^(n + 1) * (n + 1)^2)
    (h1 : S 100 = 5000) : S 21 = -281 := by
  norm_num [h] at h1 ⊢
  omega
import Mathlib

theorem algebra_170388 {f : ℕ → ℕ}
    (h₀ : ∀ n, n ≥ 1000 → f n = n - 3)
    (h₁ : ∀ n, n < 1000 → f n = f (f (n + 7))) : f 90 = 999 := by
  norm_num [h₀, h₁]
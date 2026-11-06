import Mathlib

theorem algebra_430835 {f : ℕ → ℕ → ℕ} (h1 : f 1 1 = 1)
    (h2 : ∀ m n, 0 < m → 0 < n → f m n > 0)
    (h3 : ∀ m n, 0 < m → 0 < n → f m (n + 1) = f m n + 2)
    (h4 : ∀ m, 0 < m → f (m + 1) 1 = 2 * f m 1) :
    f 11 11 = 1044 := by
  norm_num [h1, h3, h4] at *
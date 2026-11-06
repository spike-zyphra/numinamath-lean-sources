import Mathlib

theorem algebra_324942 {a : ℕ → ℤ} (ha1 : a 1 = 1) (ha2 : a 2 = 2)
    (han : ∀ n, a (n - 2) = if Even (a n * a (n - 1)) then 5 * a (n - 1) - 3 * a n else a (n - 1) - a n) :
    ∀ n, a n ≠ 0 := by
  have h1 := han 0
  have h2 := han 1
  have h3 := han 2
  have h4 := han 3
  simp [ha1, ha2] at h1 h2 h3 h4
  all_goals
    omega
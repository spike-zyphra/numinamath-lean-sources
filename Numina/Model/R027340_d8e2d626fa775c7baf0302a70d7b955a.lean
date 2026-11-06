import Mathlib

theorem algebra_228188 (x y : ℕ → ℤ)
    (hx0 : x 0 = 0) (hx1 : x 1 = 1)
    (hxn : ∀ n, x (n + 1) = 4 * x n - x (n - 1))
    (hy0 : y 0 = 1) (hy1 : y 1 = 2)
    (hy : ∀ n, y (n + 1) = 4 * y n - y (n - 1)) :
    ∀ n, (y n)^2 = 3 * (x n)^2 + 1 := by
  exfalso
  have h1 := hxn 0
  norm_num at h1 hx0 hx1
  all_goals omega
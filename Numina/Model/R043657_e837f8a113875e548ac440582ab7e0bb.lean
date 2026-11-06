import Mathlib

theorem algebra_10364 {x : ℕ → ℤ} (hx1 : x 1 = 20)
    (hxn : ∀ n, x (n + 1) = 10 * x n - 3 * 5 ^ (n + 1)) :
    x 6 = 7 * 5 ^ 5 := by
  have eq1 := hxn 0
  norm_num at eq1 hx1
  all_goals omega
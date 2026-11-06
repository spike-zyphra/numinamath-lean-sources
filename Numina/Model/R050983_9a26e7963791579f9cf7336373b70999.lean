import Mathlib

theorem algebra_196137 {x y : ℕ → ℝ}
    (hx0 : x 0 = 1) (hy0 : y 0 = 0)
    (hxn : ∀ n, x (n + 1) = x n + 2 * y n)
    (hy : ∀ n, y (n + 1) = x n + y n) :
    ∀ n, (x n)^2 - 2 * (y n)^2 = (-1)^n := by
  intro n
  induction n with
  | zero =>
    rw [hx0, hy0]
    norm_num
  | succ n ih =>
    have h1 : x (n + 1) = x n + 2 * y n := hxn n
    have h2 : y (n + 1) = x n + y n := hy n
    rw [h1, h2]
    have eq1 : (x n + 2 * y n) ^ 2 - 2 * (x n + y n) ^ 2 = - ((x n) ^ 2 - 2 * (y n) ^ 2) := by
      ring
    rw [eq1]
    have eq2 : (x n) ^ 2 - 2 * (y n) ^ 2 = (-1) ^ n := ih
    rw [eq2]
    ring_nf
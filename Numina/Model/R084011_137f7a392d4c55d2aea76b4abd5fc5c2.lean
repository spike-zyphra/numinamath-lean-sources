import Mathlib

def f (x : ℕ → ℝ) (n : ℕ) := x n - min (x (n-1)) (x (n-2))

theorem algebra_480
    (x : ℕ → ℝ)
    (hx1 : x 1 = 0)
    (hx2 : x 2 = 1)
    (hx3 : x 3 = 2)
    (hxn : ∀ n ≥ 3, f x n = x (n + 1)) :
    x 100 = 2187 := by
  have h1 : ∀ n ≥ 3, x (n + 1) = x n - min (x (n - 1)) (x (n - 2)) := by
    intro n hn
    specialize hxn n hn
    simp [f] at hxn ⊢
    linarith
  norm_num [hx1, hx2, hx3, h1] at *